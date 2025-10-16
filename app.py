# -*- coding: utf-8 -*-
from __future__ import annotations

from pathlib import Path
from datetime import datetime
from typing import Optional, Set, Tuple
from werkzeug.utils import secure_filename

from flask import (
    Flask, render_template, request, redirect, url_for,
    send_from_directory, flash, Response, make_response,
    render_template_string, redirect, abort
)

import pandas as pd
import numpy as np
import json, threading, time, queue, webbrowser, re, os, hashlib, shutil

# ==================== 경로/상수 ====================
BASE   = Path(__file__).resolve().parent
ASSETS = BASE / "assets"
SITE1  = BASE / "site1"
TPL    = BASE / "templates"
ASSETS.mkdir(parents=True, exist_ok=True)

DEFAULT_HOLDINGS = ASSETS / "소장도서목록.csv"
OUTPUT_CSV       = ASSETS / "소장도서목록_학년별대출빈도.csv"
DATA_JS          = ASSETS / "data.js"
GRADE_COLS       = [f"{i}학년" for i in range(1, 10)]

# 이미지 업로드 설정
UPLOAD_DIR = SITE1 / "images"
UPLOAD_DIR.mkdir(parents=True, exist_ok=True)

ALLOWED_EXTENSIONS = {"png", "jpg", "jpeg", "gif", "webp", "bmp"}
def allowed_file(filename: str) -> bool:
    return "." in filename and filename.rsplit(".", 1)[1].lower() in ALLOWED_EXTENSIONS

# 열 후보
CALLNUM_COL_CANDIDATES = [
    "청구기호","청구 기호","청구 번호","청구번호",
    "call_number","CallNumber","Call Number","callno","callno.","CallNo","CALL_NO"
]
UPSERT_KEY_CANDIDATES = [
    "등록번호","등록번호(바코드)","바코드","도서등록번호","도서번호","자료ID","책ID","ACCNO","Accession","accession",
    "청구기호","청구 기호","청구 번호","청구번호",
    "ISBN","ISBN13","ISBN-13","ISBN10"
]
# 매칭 키 후보군(우선순위)
KEY_GROUPS = [
    ("id",     ["등록번호","등록번호(바코드)","바코드","도서등록번호","도서번호","자료ID","책ID","ACCNO","Accession","accession"]),
    ("callno", ["청구기호","청구 기호","청구 번호","청구번호","CallNo","Call Number","CALL_NO"]),
    ("isbn",   ["ISBN","표준번호","Standard No.","ISBN13","ISBN-13","ISBN10"]),
    ("title",  ["서명","도서명","제목","자료명","Title","서명(저자)","서명/저자"]),
]

app = Flask(__name__, template_folder=str(TPL))
app.secret_key = "change-this-in-production"

# 용량 제한(선택): 10MB
app.config["MAX_CONTENT_LENGTH"] = 10 * 1024 * 1024

# ==================== SSE (data.js 버전 푸시) ====================
_data_version = 0
_subs: Set[queue.Queue] = set()
_lock = threading.Lock()

def _notify():
    global _data_version
    with _lock:
        _data_version += 1
        for q in list(_subs):
            try:
                q.put_nowait(_data_version)
            except Exception:
                pass

@app.route("/events")
def events():
    q = queue.Queue(maxsize=5)
    with _lock:
        _subs.add(q)
        cur = _data_version

    def stream():
        yield f"data: {json.dumps({'version': cur})}\n\n"
        try:
            while True:
                try:
                    ver = q.get(timeout=15)
                    yield f"data: {json.dumps({'version': ver})}\n\n"
                except queue.Empty:
                    yield ": ping\n\n"
        finally:
            with _lock:
                _subs.discard(q)

    return Response(stream(), mimetype="text/event-stream",
                    headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"})

# ==================== 파일/텍스트 유틸 ====================
def read_csv_safely(path: Path) -> pd.DataFrame:
    last = None
    for enc in ("utf-8-sig","cp949","utf-8","euc-kr","utf-16","utf-16le","utf-16be","iso-8859-1","latin1"):
        try:
            return pd.read_csv(path, encoding=enc, engine="python")
        except Exception as e:
            last = e
    try:
        return pd.read_csv(path, encoding="utf-8", engine="python", on_bad_lines="skip")
    except Exception:
        raise RuntimeError(f"CSV 열기 실패: {path}\n{last}")

def pick_first(cols, cands):
    for c in cands:
        if c in cols: return c
    return None

# --- 원자적 쓰기 + 재시도 + 해시/디바운스 ---
_build_lock = threading.Lock()
_last_build_ts = 0.0
_last_data_hash: Optional[str] = None
MIN_REBUILD_INTERVAL = 0.7  # sec

def _write_atomic_text(path: Path, text: str, encoding="utf-8"):
    tmp = path.with_suffix(path.suffix + ".tmp")
    with open(tmp, "w", encoding=encoding) as f:
        f.write(text)
        f.flush()
        os.fsync(f.fileno())
    # 교체 재시도 (Windows 파일 잠금 완화)
    for _ in range(3):
        try:
            os.replace(tmp, path)
            return
        except PermissionError:
            time.sleep(0.5)
    try:
        if path.exists():
            os.remove(path)
    except Exception:
        pass
    os.replace(tmp, path)

# ==================== 분류/보정 유틸 ====================
KDC_MAJOR = {0:"총류",1:"철학",2:"종교",3:"사회과학",4:"자연과학",5:"기술과학",6:"예술",7:"언어",8:"문학",9:"역사"}

def find_callnum_column(df: pd.DataFrame) -> str:
    cols = [str(c).strip() for c in df.columns]
    for target in CALLNUM_COL_CANDIDATES:
        if target in cols: return target
    for c in cols:
        if "청구" in c: return c
    for c in cols:
        if "call" in c.lower(): return c
    raise ValueError("청구기호 열을 찾지 못했습니다. '청구' 포함 열이 필요합니다.")

def classify_kdc_major(callnum: str) -> str:
    if not callnum: return "예외"
    t = str(callnum).strip()
    if re.match(r"^[A-Z]{1,3}\d", t): return "예외"
    head = t.split("/", 1)[0]
    m = re.search(r"(\d{3})(?:\.\d+)?", head) or re.search(r"(\d{3})(?:\.\d+)?", t)
    if m: return KDC_MAJOR.get(int(m.group(1)[0]), "예외")
    return "예외"

def classify_material_type(callnum: str) -> str:
    if not callnum: return "일반"
    t = str(callnum).strip()
    if re.match(r"^유아(\b|\s|\d|/)", t): return "유아"
    if re.match(r"^온책(\b|\s|\d|/)", t): return "온책"
    return "일반"

def add_major_and_type_columns(df: pd.DataFrame) -> pd.DataFrame:
    if df is None or df.empty: return df
    try:
        call_col = find_callnum_column(df)
    except Exception:
        if "대분류" not in df.columns: df["대분류"] = "예외"
        if "자료유형" not in df.columns: df["자료유형"] = "일반"
        return df
    s = df[call_col].astype(str).fillna("").str.strip()
    if "대분류" not in df.columns:
        df["대분류"] = s.map(classify_kdc_major)
    else:
        mask = df["대분류"].astype(str).str.strip().eq("") | df["대분류"].isna()
        df.loc[mask, "대분류"] = s.loc[mask].map(classify_kdc_major)
    if "자료유형" not in df.columns:
        df["자료유형"] = s.map(classify_material_type)
    else:
        mask = df["자료유형"].astype(str).str.strip().eq("") | df["자료유형"].isna()
        df.loc[mask, "자료유형"] = s.loc[mask].map(classify_material_type)
    return df

def ensure_grade_and_total(df: pd.DataFrame) -> pd.DataFrame:
    if df is None or df.empty: return df
    for g in GRADE_COLS:
        if g not in df.columns: df[g] = 0
        df[g] = pd.to_numeric(df[g], errors="coerce").fillna(0).astype(int)
    df["대출빈도"] = df[GRADE_COLS].sum(axis=1).astype(int)
    return df

# ==================== 키 유틸 ====================
def normalize_series(s: pd.Series) -> pd.Series:
    x = (
        s.astype(str)
         .str.replace(r"\s+", " ", regex=True)
         .str.strip()
    )
    x = x.replace({
        "": np.nan,
        "nan": np.nan, "NaN": np.nan, "NAN": np.nan,
        "none": np.nan, "None": np.nan, "NONE": np.nan,
        "nat": np.nan, "NaT": np.nan, "NAT": np.nan,
    })
    return x

def find_common_key(hold_cols, sheet_cols) -> Optional[Tuple[str,str,str]]:
    hold_cols = list(hold_cols); sheet_cols = list(sheet_cols)
    for kind, names in KEY_GROUPS:
        h = [c for c in hold_cols if c in names]
        s = [c for c in sheet_cols if c in names]
        if h and s:
            same = [c for c in h if c in s]
            if same: return kind, same[0], same[0]
            return kind, h[0], s[0]
    return None

def pick_upsert_key(df: pd.DataFrame) -> Optional[str]:
    for c in UPSERT_KEY_CANDIDATES:
        if c in df.columns: return c
    return None

# ==================== UPSERT(증분 병합) ====================
def upsert_rows(old_df: pd.DataFrame, new_df: pd.DataFrame) -> pd.DataFrame:
    """
    OUTPUT(기존) + 신규 소장 CSV를 키로 UPSERT.
    - 키 동일: 학년열은 합산, 기타는 새 값 우선(coalesce)
    - 키 미존재: 신규로 추가
    """
    if old_df is None or old_df.empty:
        res = add_major_and_type_columns(new_df.copy())
        return ensure_grade_and_total(res)

    key = pick_upsert_key(old_df) or pick_upsert_key(new_df)
    if not key:
        merged = pd.concat([old_df, new_df], ignore_index=True)
        merged = add_major_and_type_columns(merged)
        return ensure_grade_and_total(merged)

    old = old_df.copy(); new = new_df.copy()
    old[key] = normalize_series(old.get(key, pd.Series(index=old.index)))
    new[key] = normalize_series(new.get(key, pd.Series(index=new.index)))

    all_cols = list(dict.fromkeys(list(old.columns) + list(new.columns)))
    for c in all_cols:
        if c not in old.columns: old[c] = np.nan
        if c not in new.columns: new[c] = np.nan

    old = old.set_index(key); new = new.set_index(key)
    both_idx = old.index.intersection(new.index)
    only_new = new.index.difference(old.index)
    only_old = old.index.difference(new.index)

    res = old.loc[only_old].copy()

    if len(both_idx) > 0:
        o = old.loc[both_idx].copy()
        n = new.loc[both_idx].copy()
        # 학년열 합산
        for g in GRADE_COLS:
            if g not in o.columns: o[g] = 0
            if g not in n.columns: n[g] = 0
            o[g] = pd.to_numeric(o[g], errors="coerce").fillna(0) + pd.to_numeric(n[g], errors="coerce").fillna(0)
        # 기타: 새 값 우선
        for c in o.columns:
            if c in GRADE_COLS: continue
            if c in n.columns:
                o[c] = n[c].where(n[c].notna() & (n[c].astype(str).str.strip() != ""), o[c])
        res = pd.concat([res, o], axis=0)

    if len(only_new) > 0:
        res = pd.concat([res, new.loc[only_new]], axis=0)

    res = res.reset_index()
    res = add_major_and_type_columns(res)
    res = ensure_grade_and_total(res)
    # 원래 컬럼 순서를 최대한 유지
    for c in res.columns:
        if c not in all_cols: all_cols.append(c)
    return res[all_cols]

# ==================== data.js 생성 ====================
def build_data_js_legacy(csv_path: Path, out_dir: Path) -> int:
    global _last_build_ts, _last_data_hash

    now = time.time()
    if now - _last_build_ts < MIN_REBUILD_INTERVAL and DATA_JS.exists():
        return -1

    df = read_csv_safely(csv_path)
    df = add_major_and_type_columns(df)
    df = ensure_grade_and_total(df)

    COL_TITLE  = pick_first(df.columns, ["도서명","서명","제목","title","booktitle","name"])
    COL_AUTHOR = pick_first(df.columns, ["저자","저자명","작가","author","authors"])
    COL_CALLNO = pick_first(df.columns, CALLNUM_COL_CANDIDATES)
    COL_MTYPE  = pick_first(df.columns, ["자료유형","대상","type","materialtype"])
    COL_MAJOR  = pick_first(df.columns, ["대분류","주제","주제분류","분류","class","category","subject"])
    COL_FREQ   = "대출빈도"
    COL_REGNO  = pick_first(df.columns, ["등록번호","등록번호(바코드)","바코드","관리번호","Accession","등록코드","id","identifier","isbn"])
    COL_SERIES = pick_first(df.columns, ["총서명","총서 제목","총서"])
    COL_PUB    = pick_first(df.columns, ["출판사","발행자","Publisher","publisher"])

    keep = [c for c in [COL_REGNO, COL_TITLE, COL_CALLNO, COL_SERIES, COL_AUTHOR, COL_PUB, COL_MAJOR, COL_MTYPE, COL_FREQ] if c] + GRADE_COLS
    out_dir.mkdir(parents=True, exist_ok=True)

    if not keep:
        js_text = "window.CATALOG=[];window.DATA=window.CATALOG;"
        new_hash = hashlib.sha1(js_text.encode("utf-8")).hexdigest()
        with _build_lock:
            if new_hash != _last_data_hash or not DATA_JS.exists():
                _write_atomic_text(out_dir / "data.js", js_text, "utf-8")
                _last_data_hash = new_hash
                _last_build_ts = time.time()
                _notify()
        return 0

    df2 = df[keep].copy()
    rename = {}
    if COL_REGNO:  rename[COL_REGNO]  = "등록번호"
    if COL_TITLE:  rename[COL_TITLE]  = "도서명"
    if COL_CALLNO: rename[COL_CALLNO] = "청구기호"
    if COL_SERIES: rename[COL_SERIES] = "총서명"
    if COL_AUTHOR: rename[COL_AUTHOR] = "저자명"
    if COL_PUB:    rename[COL_PUB]    = "출판사"
    if COL_MAJOR:  rename[COL_MAJOR]  = "대분류"
    if COL_MTYPE:  rename[COL_MTYPE]  = "자료유형"
    if COL_FREQ:   rename[COL_FREQ]   = "대출빈도"
    df2.rename(columns=rename, inplace=True)

    df2 = ensure_grade_and_total(df2)
    for c in ["등록번호","도서명","청구기호","총서명","저자명","출판사","대분류","자료유형"]:
        if c in df2.columns:
            df2[c] = df2[c].fillna("").astype(str).str.strip()

    records = df2.to_dict(orient="records")
    json_text = json.dumps(records, ensure_ascii=False, separators=(",",":"))
    js_text = "window.CATALOG=" + json_text + ";window.DATA=window.CATALOG;"

    new_hash = hashlib.sha1(js_text.encode("utf-8")).hexdigest()
    with _build_lock:
        if new_hash == _last_data_hash and DATA_JS.exists():
            return len(records)
        _write_atomic_text(out_dir / "data.js", js_text, "utf-8")
        _last_data_hash = new_hash
        _last_build_ts = time.time()
    _notify()
    return len(records)

def rebuild_data_js_from_sources() -> int:
    if OUTPUT_CSV.exists():
        return build_data_js_legacy(OUTPUT_CSV, ASSETS)
    elif DEFAULT_HOLDINGS.exists():
        return build_data_js_legacy(DEFAULT_HOLDINGS, ASSETS)
    else:
        js_text = "window.CATALOG=[];window.DATA=window.CATALOG;"
        new_hash = hashlib.sha1(js_text.encode("utf-8")).hexdigest()
        with _build_lock:
            if new_hash != _last_data_hash or not DATA_JS.exists():
                _write_atomic_text(DATA_JS, js_text, "utf-8")
                _last_data_hash = new_hash
                _last_build_ts = time.time()
                _notify()
        return 0

# ==================== 대출기록 증분 집계 ====================
def compute_grade_counts_delta(base: pd.DataFrame, loans_xlsx: Path) -> pd.DataFrame:
    """
    XLSX의 각 학년 시트를 읽어 '신규 건수'를 집계하여 base의 학년열에 '더한다'(증분).
    공통 키는 자동 탐색, 키 값은 normalize.
    """
    base = add_major_and_type_columns(base)
    base = ensure_grade_and_total(base)

    xl = pd.ExcelFile(loans_xlsx)
    for s in GRADE_COLS:
        if s not in xl.sheet_names:
            # 시트 없으면 변화 없음(증분 0)
            base[s] = pd.to_numeric(base.get(s, 0), errors="coerce").fillna(0).astype(int)
            continue

        sh = pd.read_excel(loans_xlsx, sheet_name=s, dtype=str)
        key_info = find_common_key(base.columns, sh.columns)
        if not key_info:
            # 키 매칭 못 찾으면 변화 없음
            base[s] = pd.to_numeric(base.get(s, 0), errors="coerce").fillna(0).astype(int)
            continue

        _, hcol, scol = key_info
        hkey = normalize_series(base[hcol]) if hcol in base.columns else None
        skey = normalize_series(sh[scol])   if scol in sh.columns   else None
        if hkey is None or skey is None:
            base[s] = pd.to_numeric(base.get(s, 0), errors="coerce").fillna(0).astype(int)
            continue

        # 신규건 카운트
        inc_map = skey.value_counts(dropna=True).to_dict()
        # 기존값 + 증가분
        old_vals = pd.to_numeric(base.get(s, 0), errors="coerce").fillna(0).astype(int)
        inc_vals = hkey.map(inc_map).fillna(0).astype(int)
        base[s] = (old_vals + inc_vals).astype(int)

    base = ensure_grade_and_total(base)
    return base

# ==================== 파이프라인 (무조건 증분) ====================
def run_pipeline_incremental(holdings_csv: Optional[Path], loans_xlsx: Optional[Path]) -> dict:
    """
    항상 증분:
    - 베이스: OUTPUT_CSV 있으면 우선, 없으면 DEFAULT_HOLDINGS, 그것도 없으면 업로드 CSV
    - holdings_csv가 오면: 베이스에 UPSERT(학년열 합산, 기타 신값 우선)
    - loans_xlsx가 오면: 베이스(또는 업서트 결과)에 '신규 건수'를 더함
    - 최종 OUTPUT_CSV 저장 → data.js 갱신
    """
    # 1) 베이스 확보
    if OUTPUT_CSV.exists():
        base = read_csv_safely(OUTPUT_CSV)
    elif DEFAULT_HOLDINGS.exists():
        base = read_csv_safely(DEFAULT_HOLDINGS)
    elif holdings_csv and Path(holdings_csv).exists():
        base = read_csv_safely(holdings_csv)
    else:
        raise FileNotFoundError("기준 파일이 없습니다. OUTPUT_CSV / DEFAULT_HOLDINGS / 업로드 holdings_csv 중 하나가 필요합니다.")

    base = add_major_and_type_columns(base)
    base = ensure_grade_and_total(base)

    # 2) 소장 CSV 업서트(선택)
    if holdings_csv and Path(holdings_csv).exists():
        new_hold = read_csv_safely(holdings_csv)
        base = upsert_rows(base, new_hold)  # 학년열 합산 + 기타 신값 우선

    # 3) 대출 XLSX 증분(선택)
    if loans_xlsx and Path(loans_xlsx).exists():
        base = compute_grade_counts_delta(base, loans_xlsx)

    # 4) 저장 + data.js 갱신
    #    (Windows 잠금 완화 위해 텍스트 원자쓰기와 동일 전략 사용)
    tmp_out = OUTPUT_CSV.with_suffix(OUTPUT_CSV.suffix + ".tmp")
    base.to_csv(tmp_out, index=False, encoding="utf-8-sig")
    for _ in range(3):
        try:
            os.replace(tmp_out, OUTPUT_CSV)
            break
        except PermissionError:
            time.sleep(0.5)
    else:
        try:
            if OUTPUT_CSV.exists():
                os.remove(OUTPUT_CSV)
        except Exception:
            pass
        os.replace(tmp_out, OUTPUT_CSV)

    cnt = rebuild_data_js_from_sources()
    return {"output": str(OUTPUT_CSV), "count": cnt, "time": datetime.now().strftime("%F %T")}

# ==================== 템플릿 컨텍스트 ====================
def _assets_ctx():
    items = []
    for p in ASSETS.glob("*"):
        if p.is_file():
            stat = p.stat()
            items.append({
                "name": p.name,
                "size": f"{stat.st_size:,} B",
                "mtime": datetime.fromtimestamp(stat.st_mtime).strftime("%Y-%m-%d %H:%M:%S"),
            })
    items.sort(key=lambda x: x["name"].lower())
    return {
        "assets": items,
        "default_holdings_exists": DEFAULT_HOLDINGS.exists(),
        "output_exists": OUTPUT_CSV.exists(),
        "output_name": OUTPUT_CSV.name if OUTPUT_CSV.exists() else "",
    }

# ==================== 라우팅 ====================
@app.route("/")
def home():
    return redirect("/site1/")

# ---- site1: 정적 서비스 ----
@app.route("/site1")
def site1_noslash():
    return redirect("/site1/")

@app.route("/site1/")
def site1_index():
    return send_from_directory(SITE1, "index.html")

@app.route("/site1/<path:filename>")
def site1_files(filename):
    resp = make_response(send_from_directory(SITE1, filename))
    resp.headers["Cache-Control"] = "no-cache"
    return resp

@app.route("/uploadpicture", methods=["GET", "POST"])
def upload_image():
    """
    - GET: 업로드 폼 + 갤러리(카드)
    - POST: 여러 파일 업로드(원본 이름 유지, 허용 확장자만), 결과 리스트 표시
    """
    # ---------------- GET ----------------
    if request.method == "GET":
        files = sorted([p.name for p in UPLOAD_DIR.iterdir() if p.is_file()])

        return render_template_string("""
<!doctype html>
<html lang="ko">
<head>
  <meta charset="utf-8">
  <title>이미지 업로드</title>
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <style>
    :root {--bg:#f7f8fb;--card:#ffffff;--text:#0f172a;--muted:#6b7280;
      --border:#e5e7eb;--accent:#111827;}
    *{box-sizing:border-box}
    body{margin:0;background:var(--bg);color:var(--text);
      font-family:ui-sans-serif,system-ui,-apple-system,Segoe UI,Roboto,Noto Sans KR,Arial}
    .wrap{max-width:980px;margin:40px auto;padding:24px;background:var(--card);
      border-radius:18px;box-shadow:0 12px 34px rgba(0,0,0,.08)}
    h1{margin:0 0 6px;font-size:28px}
    .sub{color:var(--muted);font-size:14px;margin-bottom:18px}

    form{display:flex;gap:12px;align-items:center;
      padding:14px 0 18px;border-bottom:1px solid var(--border)}
    input[type=file]{flex:1}
    button{border:0;padding:10px 16px;border-radius:10px;background:var(--accent);
      color:#fff;font-weight:700;cursor:pointer}
    button:hover{filter:brightness(1.05)}

    h2{font-size:18px;margin:22px 0 12px}
    .grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(200px,1fr));gap:18px}

    /* 카드 미려화 */
    .card{
      display:flex;flex-direction:column;align-items:center;justify-content:flex-start;
      background:#fff;border:1px solid var(--border);border-radius:16px;padding:14px;
      box-shadow:0 2px 10px rgba(0,0,0,.06);transition:transform .12s ease, box-shadow .12s ease
    }
    .card:hover{transform:translateY(-3px);box-shadow:0 8px 20px rgba(0,0,0,.10)}
    .thumb{
      width:100%;aspect-ratio:1/1;object-fit:cover;border-radius:12px;margin-bottom:10px;
      background:#eef2f7;display:block
    }
    .name{font-size:14px;font-weight:700;color:#111827;word-break:break-all;margin-bottom:8px;text-align:center}

    /* 버튼/툴바 */
    .toolbar{display:flex;gap:8px;justify-content:center;flex-wrap:wrap}
    .btn{border:none;border-radius:10px;padding:8px 14px;font-weight:700;cursor:pointer;
      transition:transform .08s ease}
    .btn:hover{transform:translateY(-2px)}
    .btn.open{background:#111827;color:#fff}
    .btn.delete{background:#ef4444;color:#fff}
    form.inline{display:inline}
    
    /* 좌우 끝으로 벌리기 + 버튼 높이 통일 */
    .card .toolbar{
    display:flex;
    align-items:center;
    width:100%;
    gap:0;                 /* 간격은 버튼 패딩으로 처리 */
    }

    .card .toolbar .btn{
    display:inline-flex;   /* a / button 동일 박스 */
    align-items:center;
    justify-content:center;
    height:36px;           /* 동일 높이 */
    min-width:84px;        /* 폭 느낌 맞춤 */
    padding:0 12px;        /* 좌우만 */
    font-size:13px;
    font-weight:700;
    line-height:1;
    border-radius:10px;
    box-sizing:border-box;
    text-decoration:none;  /* 링크 밑줄 제거 */
    }

    .card .toolbar button.btn{
    appearance:none; -webkit-appearance:none;
    margin:0; font-family:inherit;
    }

    /* 오른쪽으로 밀기용 */
    .card .toolbar .right{ margin-left:auto; }


    .empty{color:var(--muted)}
  </style>
</head>
<body>
  <div class="wrap">
    <h1>이미지 업로드</h1>
    <div class="sub">최대 10MB · png, jpg, jpeg, gif, webp, bmp</div>

    <form method="post" enctype="multipart/form-data">
      <input type="file" name="file" accept="image/*" multiple>
      <button type="submit">업로드</button>
    </form>

    <h2>업로드된 이미지</h2>

    {% if files %}
      <div class="grid">
        {% for f in files %}
          {% set u = url_for('site1_files', filename='images/' + f) %}
          <div class="card" title="{{ f }}">
            <a href="{{ u }}" target="_blank">
              <img class="thumb" src="{{ u }}" alt="{{ f }}">
            </a>
            <div class="name">{{ f }}</div>
            <div class="toolbar">
            <a class="btn open" href="{{ u }}" target="_blank">열기</a>
            <form class="inline right" action="{{ url_for('delete_image') }}" method="post"
                    onsubmit="return confirm('정말 삭제할까요? {{ f }}');">
                <input type="hidden" name="name" value="{{ f }}">
                <button type="submit" class="btn delete">삭제</button>
            </form>
            </div>
          </div>
        {% endfor %}
      </div>
    {% else %}
      <p class="empty">아직 업로드된 이미지가 없습니다.</p>
    {% endif %}
  </div>
</body>
</html>
        """, files=files)

    # ---------------- POST ----------------
    files = request.files.getlist("file")
    if not files or all((not f) or f.filename == "" for f in files):
        # 파일 미선택 시 GET 화면으로 돌려보냄
        return redirect(url_for("upload_image"))

    def _fmt_size(n: int) -> str:
        for unit in ("B", "KB", "MB", "GB"):
            if n < 1024 or unit == "GB":
                return (f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}")
            n /= 1024

    uploaded = []
    for f in files:
        if not f or f.filename == "":
            continue
        if not allowed_file(f.filename):
            continue
        filename = secure_filename(f.filename)             # 옵션 A: 원본 파일명 유지
        save_path = UPLOAD_DIR / filename
        f.save(save_path)

        url = url_for("site1_files", filename=f"images/{save_path.name}", _external=True)
        size = _fmt_size(save_path.stat().st_size)
        uploaded.append({"name": save_path.name, "url": url, "size": size})

    if not uploaded:
        # 모두 거부(확장자 등)되면 GET으로
        return redirect(url_for("upload_image"))

    return render_template_string("""
<!doctype html>
<html lang="ko">
<head>
  <meta charset="utf-8">
  <title>업로드 완료</title>
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <style>
    :root{--bg:#f7f8fb;--card:#fff;--text:#0f172a;--muted:#6b7280;--border:#e5e7eb;--accent:#111827;}
    *{box-sizing:border-box}
    body{margin:0;background:var(--bg);color:var(--text);
      font-family:ui-sans-serif,system-ui,-apple-system,Segoe UI,Roboto,Noto Sans KR,Arial}
    .wrap{max-width:980px;margin:40px auto;padding:24px;background:var(--card);
      border-radius:18px;box-shadow:0 12px 34px rgba(0,0,0,.08)}
    h1{margin:0 0 10px;font-size:28px}
    .sub{color:var(--muted);margin-bottom:18px}
    .btn{display:inline-block;text-decoration:none;border:0;background:#111827;color:#fff;
      padding:10px 14px;border-radius:12px;font-weight:700}
    .btn:hover{filter:brightness(1.05)}
    .grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:18px}

    .card{background:#fff;border:1px solid var(--border);border-radius:16px;padding:14px;
      box-shadow:0 2px 10px rgba(0,0,0,.06)}
    .thumb{width:100%;aspect-ratio:4/3;object-fit:cover;border-radius:12px;background:#eef2f7}
    .name{font-weight:700;margin:8px 0 4px;word-break:break-all}
    .size{color:var(--muted);font-size:13px;margin-bottom:8px}
    .link{display:block;word-break:break-all;color:#2563eb;text-decoration:none;margin-bottom:10px}

    .toolbar{display:flex;gap:8px;flex-wrap:wrap}
    .btn.small{padding:8px 12px;border-radius:10px}
    .btn.danger{background:#ef4444}
    form.inline{display:inline}
  </style>
</head>
<body>
  <div class="wrap">
    <h1>✅ 업로드 완료 ({{ uploaded|length }}개)</h1>
    <div class="sub"><a class="btn" href="{{ back }}">다른 이미지 업로드</a></div>

    <div class="grid">
      {% for it in uploaded %}
      <div class="card">
        <a href="{{ it.url }}" target="_blank"><img class="thumb" src="{{ it.url }}" alt="{{ it.name }}"></a>
        <div class="name">{{ it.name }}</div>
        <div class="size">{{ it.size }}</div>
        <a class="link" href="{{ it.url }}" target="_blank">{{ it.url }}</a>
        <div class="toolbar">
          <a class="btn small" href="{{ it.url }}" target="_blank">열기</a>
          <form class="inline" action="{{ url_for('delete_image') }}" method="post"
                onsubmit="return confirm('정말 삭제할까요? {{ it.name }}');">
            <input type="hidden" name="name" value="{{ it.name }}">
            <button type="submit" class="btn small danger">삭제</button>
          </form>
        </div>
      </div>
      {% endfor %}
    </div>
  </div>
</body>
</html>
    """, uploaded=uploaded, back=url_for("upload_image"))



@app.route("/removepicture", methods=["POST"], endpoint="delete_image")  # ← 슬래시 추가 + endpoint 고정
def delete_image():
    name = request.form.get("name", "")
    if not name:
        return "파일명이 없습니다.", 400
    if name != secure_filename(name):
        abort(400)

    path = UPLOAD_DIR / name
    try:
        path.resolve().relative_to(UPLOAD_DIR.resolve())
    except Exception:
        abort(400)

    if not path.exists() or not path.is_file():
        return "파일이 존재하지 않습니다.", 404

    try:
        path.unlink()
    except PermissionError:
        return "파일을 삭제할 수 없습니다(다른 프로그램이 사용 중일 수 있음).", 423

    return redirect(url_for("upload_image"))

# ---- site2: 템플릿 ----
@app.route("/uploaddata/")
def site2_index():
    if not (TPL / "index.html").exists():
        return "templates/index.html 없음", 404
    return render_template("index.html", **_assets_ctx())

@app.route("/site2/result")
def site2_result():
    if not (TPL / "result.html").exists():
        return "templates/result.html 없음", 404
    return render_template("result.html", **_assets_ctx())

# ---- 공유 assets ----
@app.route("/assets/<path:filename>")
def assets_files(filename):
    resp = make_response(send_from_directory(ASSETS, filename))
    resp.headers["Cache-Control"] = "no-cache"
    return resp

# ---- 업로드(증분 파이프라인) ----
@app.route("/upload", methods=["POST"])
def upload():
    h = request.files.get("holdings_csv")  # 선택
    x = request.files.get("loans_xlsx")    # 선택
    if not (h and h.filename) and not (x and x.filename):
        flash("업로드할 파일이 없습니다. CSV 또는 XLSX 중 하나는 올려주세요.")
        return redirect(url_for("site2_index"))

    path_h = None
    if h and h.filename:
        path_h = ASSETS / Path(h.filename).name
        h.save(path_h)

    path_x = None
    if x and x.filename:
        if not x.filename.endswith(".xlsx"):
            flash("대출기록은 .xlsx 파일이어야 합니다.")
            return redirect(url_for("site2_index"))
        path_x = ASSETS / Path(x.filename).name
        x.save(path_x)

    try:
        summary = run_pipeline_incremental(path_h, path_x)
        flash(f"[증분 완료] data.js 반영: {summary.get('count',0)}권, 저장: {summary.get('output')}")
    except Exception as e:
        flash(f"오류: {e}")
    return redirect(url_for("site2_index"))

# ---- 관리자: 추가 CSV 업서트 전용 (선택 사용) ----
@app.route("/admin/upsert", methods=["POST"])
def admin_upsert():
    f = request.files.get("append_csv")
    if not f or not f.filename.endswith(".csv"):
        return {"ok": False, "msg": "CSV 파일을 올려주세요(필드명 append_csv)."}, 400

    path_new = ASSETS / Path(f.filename).name
    f.save(path_new)

    new_df = read_csv_safely(path_new)
    if OUTPUT_CSV.exists():
        old_df = read_csv_safely(OUTPUT_CSV)
        merged = upsert_rows(old_df, new_df)
    else:
        merged = ensure_grade_and_total(add_major_and_type_columns(new_df))

    tmp_out = OUTPUT_CSV.with_suffix(OUTPUT_CSV.suffix + ".tmp")
    merged.to_csv(tmp_out, index=False, encoding="utf-8-sig")
    for _ in range(3):
        try:
            os.replace(tmp_out, OUTPUT_CSV)
            break
        except PermissionError:
            time.sleep(0.5)
    else:
        try:
            if OUTPUT_CSV.exists():
                os.remove(OUTPUT_CSV)
        except Exception:
            pass
    os.replace(tmp_out, OUTPUT_CSV)

    cnt = rebuild_data_js_from_sources()
    return {"ok": True, "output": str(OUTPUT_CSV), "count": cnt}

# ---- 상태/디버그 ----
@app.route("/download/output")
def download_output():
    if not OUTPUT_CSV.exists():
        return "OUTPUT CSV 없음", 404
    return send_from_directory(ASSETS, OUTPUT_CSV.name, as_attachment=True)

@app.route("/health")
def health():
    return {"status": "ok", "version": _data_version, "time": datetime.now().isoformat()}

@app.route("/debug/columns")
def dbg_cols():
    src = OUTPUT_CSV if OUTPUT_CSV.exists() else (DEFAULT_HOLDINGS if DEFAULT_HOLDINGS.exists() else None)
    if not src or not src.exists():
        return {"columns": [], "rows": 0, "source": None}
    df = read_csv_safely(src)
    return {"columns": list(df.columns), "rows": int(df.shape[0]), "source": str(src.name)}

@app.route("/debug/sample")
def dbg_sample():
    src = OUTPUT_CSV if OUTPUT_CSV.exists() else (DEFAULT_HOLDINGS if DEFAULT_HOLDINGS.exists() else None)
    if not src or not src.exists():
        return {"head": [], "source": None}
    df = read_csv_safely(src)
    return {"head": df.head(5).to_dict(orient="records"), "source": str(src.name)}

@app.route("/admin/rebuild")
def admin_rebuild():
    n = rebuild_data_js_from_sources()
    return {"ok": True, "version": _data_version, "count": n}

# ==================== 파일 변경 감시 ====================
def watch_output():
    """OUTPUT_CSV 변경 또는 data.js 부재 시 자동 재생성"""
    last = OUTPUT_CSV.stat().st_mtime if OUTPUT_CSV.exists() else None
    while True:
        try:
            if OUTPUT_CSV.exists():
                m = OUTPUT_CSV.stat().st_mtime
                if m != last or not DATA_JS.exists():
                    last = m
                    rebuild_data_js_from_sources()
            else:
                if not DATA_JS.exists():
                    rebuild_data_js_from_sources()
        except Exception:
            pass
        time.sleep(0.7)

# ==================== 실행 ====================
if __name__ == "__main__":
    try:
        rebuild_data_js_from_sources()
    except Exception:
        pass

    threading.Thread(target=watch_output, daemon=True).start()
#    threading.Timer(1.0, lambda: webbrowser.open_new("http://127.0.0.1:5000/site1/")).start()
    app.run(host="127.0.0.1", port=5000, debug=False, use_reloader=False)
