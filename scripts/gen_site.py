#!/usr/bin/env python3
"""Generate the static GitHub Pages dashboard into build/site/.

Reads the same sources as gen_readme.py (problems/*/status.yaml and
docs/highlights.yaml) and renders a self-contained bilingual dashboard:
build/site/index.html (English) and build/site/ko/index.html (Korean).
Nothing under build/ is committed; CI regenerates and deploys the site on
every green push to main (see .github/workflows/verify.yml).
"""
import datetime
import html
import os
import sys
from pathlib import Path

import gen_readme as gr

REPO_URL = "https://github.com/umaia1234/agentic-conjectures"
OUT = gr.ROOT / "build" / "site"
STATUS_ORDER = ["proved", "refuted", "partial", "open"]

STR = {
    "en": {
        "lang": "en",
        "title": "Agentic Conjectures — live dashboard",
        "description": (
            "The agent chooses the problem. CI chooses whether mathematics "
            "happened. Machine-verified results from autonomous agents "
            "attacking open conjectures."
        ),
        "tagline": "The agent chooses the problem. "
                   "CI chooses whether mathematics happened.",
        "sub": (
            "Autonomous agents pick open problems and conjectures, attack "
            "them, and accumulate results only in machine-verifiable form. "
            "Every claim below is re-verified by CI on every push or labeled "
            "as exactly what it is. Everything is unreviewed and claims no "
            "novelty."
        ),
        "switch": '<strong>English</strong> · <a href="ko/">한국어</a>',
        "repo": "GitHub ↗",
        "problems": "problems",
        "highlights": "🏅 This week's highlights",
        "archive": "all past weeks",
        "search": "Search problems, claims, models…",
        "all_domains": "All domains",
        "all_statuses": "All statuses",
        "shown": "shown",
        "th": ["Problem", "Domain", "Claimed status", "Machine checks",
               "Solved by", "Claim"],
        "foot_note": "A claim CI does not verify is just a claim.",
        "foot_meta": "Unreviewed machine-assisted work · no novelty or "
                     "priority claimed · Apache-2.0",
        "generated": "Generated",
        "from_commit": "from",
    },
    "ko": {
        "lang": "ko",
        "title": "Agentic Conjectures — 라이브 대시보드",
        "description": (
            "에이전트가 문제를 고르고, CI가 수학이 일어났는지 판정합니다. "
            "자율 에이전트가 공개 추측을 공략해 얻은 기계 검증 결과."
        ),
        "tagline": "에이전트가 문제를 고르고, CI가 수학이 일어났는지 판정합니다.",
        "sub": (
            "자율 에이전트가 공개 미해결 문제·추측을 골라 공격하고, 결과를 "
            "기계 검증 가능한 형태로만 축적합니다. 아래 모든 주장은 푸시할 "
            "때마다 CI가 재검증하거나, 아니면 정확히 있는 그대로 표기됩니다. "
            "모든 결과는 동료 검토 전이며 novelty를 주장하지 않습니다."
        ),
        "switch": '<a href="../">English</a> · <strong>한국어</strong>',
        "repo": "GitHub ↗",
        "problems": "문제",
        "highlights": "🏅 이번 주 하이라이트",
        "archive": "지난 주간 기록",
        "search": "문제·주장·모델 검색…",
        "all_domains": "모든 분야",
        "all_statuses": "모든 상태",
        "shown": "표시",
        "th": ["문제", "분야", "주장 상태", "기계 검증", "작업 모델", "주장"],
        "foot_note": "CI가 검증하지 않은 주장은 주장일 뿐입니다.",
        "foot_meta": "동료 검토 전의 기계 보조 작업 · novelty·우선권 주장 "
                     "없음 · Apache-2.0",
        "generated": "생성:",
        "from_commit": "커밋",
    },
}

CSS = """
*{box-sizing:border-box}
:root{
  --bg:#f6f8fa; --surface:#ffffff; --border:#d0d7de; --ink:#1f2328;
  --ink2:#59636e; --accent:#0969da;
  --proved-fg:#116329; --proved-bg:#dafbe1;
  --refuted-fg:#a40e26; --refuted-bg:#ffebe9;
  --partial-fg:#7d4e00; --partial-bg:#fff8c5;
  --open-fg:#424a53; --open-bg:#eaeef2;
}
@media (prefers-color-scheme: dark){
  :root{
    --bg:#0d1117; --surface:#161b22; --border:#30363d; --ink:#e6edf3;
    --ink2:#9198a1; --accent:#4493f8;
    --proved-fg:#3fb950; --proved-bg:rgba(46,160,67,.16);
    --refuted-fg:#f85149; --refuted-bg:rgba(248,81,73,.16);
    --partial-fg:#d29922; --partial-bg:rgba(187,128,9,.18);
    --open-fg:#9198a1; --open-bg:rgba(139,148,158,.16);
  }
}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--ink);
  font:15px/1.55 -apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,Arial,
  "Apple SD Gothic Neo","Malgun Gothic",sans-serif}
a{color:var(--accent);text-decoration:none}
a:hover{text-decoration:underline}
code{font-family:ui-monospace,SFMono-Regular,"SF Mono",Menlo,Consolas,
  monospace;font-size:.92em}
.wrap{max-width:1140px;margin:0 auto;padding:0 20px}
.hero{background:#0d1117;color:#e6edf3;border-bottom:1px solid #30363d;
  padding:28px 0 30px}
.hero .topbar{display:flex;justify-content:space-between;align-items:center;
  font-size:13.5px;margin-bottom:22px;color:#9198a1}
.hero .topbar a{color:#9198a1}
.hero .topbar strong{color:#e6edf3}
.hero .gh{border:1px solid #30363d;border-radius:6px;padding:5px 12px}
.hero .gh:hover{border-color:#8b949e;text-decoration:none;color:#e6edf3}
.hero .logo{display:block;max-width:100%;height:auto;margin:0 auto}
.hero .tagline{text-align:center;font-weight:600;font-size:17px;
  margin:14px 0 8px;color:#e6edf3}
.hero .sub{text-align:center;max-width:760px;margin:0 auto;color:#9198a1;
  font-size:14px}
.tiles{display:grid;grid-template-columns:repeat(5,1fr);gap:10px;
  margin:22px 0 18px}
.tile{appearance:none;border:1px solid var(--border);background:var(--surface);
  border-radius:10px;padding:12px 8px 10px;cursor:pointer;text-align:center;
  color:var(--ink);font:inherit;border-top:3px solid var(--tint,var(--border))}
.tile .n{display:block;font-size:26px;font-weight:700;line-height:1.15}
.tile .l{display:block;font-size:12.5px;color:var(--ink2);margin-top:2px}
.tile[aria-pressed="true"]{outline:2px solid var(--accent);outline-offset:-1px}
.tile:hover{border-color:var(--accent)}
.tile.proved{--tint:var(--proved-fg)} .tile.refuted{--tint:var(--refuted-fg)}
.tile.partial{--tint:var(--partial-fg)} .tile.open{--tint:var(--open-fg)}
.card{background:var(--surface);border:1px solid var(--border);
  border-radius:10px;padding:16px 20px;margin:0 0 18px}
.card h2{margin:0 0 4px;font-size:17px}
.card .curator{margin:0 0 10px;color:var(--ink2);font-size:13.5px}
.card ul{margin:0;padding:0;list-style:none}
.card li{padding:9px 0;border-top:1px solid var(--border)}
.card li .blurb{margin:3px 0 0;color:var(--ink2);font-size:13.5px}
.pill{display:inline-block;border-radius:999px;padding:1.5px 9px;
  font-size:12px;font-weight:600;white-space:nowrap}
.pill.proved{color:var(--proved-fg);background:var(--proved-bg)}
.pill.refuted{color:var(--refuted-fg);background:var(--refuted-bg)}
.pill.partial{color:var(--partial-fg);background:var(--partial-bg)}
.pill.open{color:var(--open-fg);background:var(--open-bg)}
.checks{color:var(--ink2);font-size:12px;white-space:nowrap}
.controls{display:flex;gap:10px;align-items:center;flex-wrap:wrap;
  margin:0 0 12px}
.controls input[type=search]{flex:1;min-width:220px;padding:7px 12px;
  border:1px solid var(--border);border-radius:8px;background:var(--surface);
  color:var(--ink);font:inherit}
.controls select{padding:7px 10px;border:1px solid var(--border);
  border-radius:8px;background:var(--surface);color:var(--ink);font:inherit}
.controls .count{color:var(--ink2);font-size:13px;margin-left:auto}
.tablewrap{overflow-x:auto;border:1px solid var(--border);border-radius:10px;
  background:var(--surface)}
table{border-collapse:collapse;width:100%;min-width:980px}
th{position:sticky;top:0;background:var(--surface);text-align:left;
  font-size:12.5px;color:var(--ink2);border-bottom:1px solid var(--border);
  padding:9px 12px;white-space:nowrap}
td{border-top:1px solid var(--border);padding:9px 12px;vertical-align:top;
  font-size:13.5px}
tr:first-child td{border-top:0}
td.t{min-width:240px;font-weight:600}
td.d{white-space:nowrap;color:var(--ink2)}
td.m{font-size:12.5px;color:var(--ink2)}
td.claim{min-width:340px;max-width:560px;color:var(--ink2)}
.foot{padding:22px 20px 34px;color:var(--ink2);font-size:13px;
  text-align:center}
.foot strong{color:var(--ink)}
@media (max-width:760px){
  .tiles{grid-template-columns:repeat(2,1fr)}
  .tiles .tile.all{grid-column:1 / -1}
}
"""

JS = """
(function(){
  var rows=[].slice.call(document.querySelectorAll('#tbl tbody tr'));
  var q=document.getElementById('q'), dom=document.getElementById('domain'),
      st=document.getElementById('status'),
      count=document.getElementById('count'),
      shown=count.getAttribute('data-shown'),
      tiles=[].slice.call(document.querySelectorAll('.tile'));
  function apply(){
    var needle=q.value.trim().toLowerCase(), d=dom.value, s=st.value, n=0;
    rows.forEach(function(r){
      var ok=(!needle||r.getAttribute('data-text').indexOf(needle)>=0)&&
             (!d||r.getAttribute('data-domain')===d)&&
             (!s||r.getAttribute('data-status')===s);
      r.hidden=!ok; if(ok)n++;
    });
    count.textContent=n+' / '+rows.length+' '+shown;
    tiles.forEach(function(t){
      t.setAttribute('aria-pressed', String(t.getAttribute('data-status')===s));
    });
  }
  tiles.forEach(function(t){
    t.addEventListener('click', function(){
      var v=t.getAttribute('data-status');
      st.value=(st.value===v?'':v); apply();
    });
  });
  [q,dom,st].forEach(function(el){ el.addEventListener('input', apply); });
  apply();
})();
"""


def e(s: str) -> str:
    return html.escape(str(s), quote=True)


def problem_url(status: dict, locale: str) -> str:
    name = gr.localized_problem_file(status, "README.md", locale)
    return f"{REPO_URL}/blob/main/problems/{status['id']}/{name}"


def pill(status: dict, locale: str) -> str:
    st = status.get("claimed_status", "open")
    return f'<span class="pill {e(st)}">{e(gr.BADGE[locale][st])}</span>'


def tiles_html(counts: dict, total: int, locale: str) -> str:
    t = STR[locale]
    tiles = [
        f'<button class="tile all" data-status="" aria-pressed="true">'
        f'<span class="n">{total}</span>'
        f'<span class="l">{e(t["problems"])}</span></button>'
    ]
    for st in STATUS_ORDER:
        tiles.append(
            f'<button class="tile {st}" data-status="{st}" aria-pressed="false">'
            f'<span class="n">{counts.get(st, 0)}</span>'
            f'<span class="l">{e(gr.BADGE[locale][st])}</span></button>'
        )
    return "\n".join(tiles)


def highlights_html(weeks: list, by_id: dict, locale: str) -> str:
    t = STR[locale]
    week = weeks[-1]
    blurb_key = "blurb_ko" if locale == "ko" else "blurb"
    title_key = "title_ko" if locale == "ko" else "title"
    archive = "HIGHLIGHTS.ko.md" if locale == "ko" else "HIGHLIGHTS.md"
    items = []
    for pick in week["picks"]:
        s = by_id[pick["problem"]]
        checks = gr.checks_cell(s, locale)
        tag = f' <span class="checks"><code>{e(checks)}</code></span>' \
            if checks != "—" else ""
        items.append(
            f"<li>{pill(s, locale)} "
            f'<a href="{e(problem_url(s, locale))}">'
            f"{e(s.get(title_key, s.get('title', s['id'])))}</a>{tag}"
            f'<p class="blurb">{e(pick[blurb_key])}</p></li>'
        )
    return (
        f'<section class="card"><h2>{t["highlights"]}</h2>'
        f'<p class="curator">{e(gr.curator_heading(week, locale))} · '
        f'<a href="{REPO_URL}/blob/main/docs/{archive}">{e(t["archive"])}</a>'
        f"</p><ul>{''.join(items)}</ul></section>"
    )


def row_html(status: dict, locale: str) -> str:
    title_key = "title_ko" if locale == "ko" else "title"
    claim_key = "claim_ko" if locale == "ko" else "claim"
    domain = status.get("domain")
    domain = domain if domain in gr.DOMAIN_ORDER else "other"
    title = status.get(title_key, status.get("title", status["id"]))
    claim = status.get(claim_key, status.get("claim", ""))
    models = " · ".join(
        a.get("model", "") for a in status.get("attribution") or []
        if a.get("model")
    ) or "—"
    checks = gr.checks_cell(status, locale)
    haystack = " ".join([
        status["id"], title, claim, models, checks,
        status.get("claimed_status", "open"),
        gr.DOMAIN_TITLE[locale][domain],
    ]).lower()
    return (
        f'<tr data-status="{e(status.get("claimed_status", "open"))}" '
        f'data-domain="{e(domain)}" data-text="{e(haystack)}">'
        f'<td class="t"><a href="{e(problem_url(status, locale))}">'
        f"{e(title)}</a></td>"
        f'<td class="d">{e(gr.DOMAIN_TITLE[locale][domain])}</td>'
        f"<td>{pill(status, locale)}</td>"
        f'<td class="m">{e(checks)}</td>'
        f'<td class="m">{e(models)}</td>'
        f'<td class="claim">{e(claim)}</td></tr>'
    )


def page(statuses, weeks, by_id, locale: str, logo: str,
         stamp: str, commit: str) -> str:
    t = STR[locale]
    counts = dict.fromkeys(STATUS_ORDER, 0)
    for s in statuses:
        st = s.get("claimed_status", "open")
        counts[st] = counts.get(st, 0) + 1
    domain_opts = "".join(
        f'<option value="{d}">{e(gr.DOMAIN_TITLE[locale][d])}</option>'
        for d in gr.DOMAIN_ORDER
    )
    status_opts = "".join(
        f'<option value="{st}">{e(gr.BADGE[locale][st])}</option>'
        for st in STATUS_ORDER
    )
    rows = "\n".join(row_html(s, locale) for s in statuses)
    ths = "".join(f"<th>{e(h)}</th>" for h in t["th"])
    if commit:
        commit_html = (f'<a href="{REPO_URL}/commit/{e(commit)}">'
                       f"<code>{e(commit[:7])}</code></a>")
    else:
        commit_html = "<code>local</code>"
    return f"""<!doctype html>
<html lang="{t['lang']}">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{e(t['title'])}</title>
<meta name="description" content="{e(t['description'])}">
<style>{CSS}</style>
</head>
<body>
<header class="hero"><div class="wrap">
<div class="topbar"><span>{t['switch']}</span>
<a class="gh" href="{REPO_URL}">{e(t['repo'])}</a></div>
{logo}
<p class="tagline">{e(t['tagline'])}</p>
<p class="sub">{e(t['sub'])}</p>
</div></header>
<main class="wrap">
<section class="tiles" aria-label="{e(t['problems'])}">
{tiles_html(counts, len(statuses), locale)}
</section>
{highlights_html(weeks, by_id, locale)}
<section class="controls">
<input id="q" type="search" placeholder="{e(t['search'])}">
<select id="domain" aria-label="domain"><option value="">{e(t['all_domains'])}</option>{domain_opts}</select>
<select id="status" aria-label="status"><option value="">{e(t['all_statuses'])}</option>{status_opts}</select>
<span id="count" class="count" data-shown="{e(t['shown'])}"></span>
</section>
<div class="tablewrap"><table id="tbl">
<thead><tr>{ths}</tr></thead>
<tbody>
{rows}
</tbody>
</table></div>
</main>
<footer class="foot wrap">
<p><strong>{e(t['foot_note'])}</strong><br>
{e(t['foot_meta'])}<br>
{e(t['generated'])} {e(stamp)} {e(t['from_commit'])} {commit_html} ·
<a href="{REPO_URL}">github.com/umaia1234/agentic-conjectures</a></p>
</footer>
<script>{JS}</script>
</body>
</html>
"""


def main() -> int:
    statuses = gr.load_statuses()
    by_id = {s["id"]: s for s in statuses}
    weeks, errors = gr.load_highlights(by_id)
    if errors:
        print("invalid weekly highlights data:")
        for error in errors:
            print(f"  {error}")
        return 1
    logo_svg = (gr.ROOT / "assets" / "logo.svg").read_text(encoding="utf-8")
    logo = logo_svg.replace("<svg ", '<svg class="logo" ', 1)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime(
        "%Y-%m-%d %H:%M UTC")
    commit = os.environ.get("GITHUB_SHA", "")
    for locale, path in (("en", OUT / "index.html"),
                         ("ko", OUT / "ko" / "index.html")):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            page(statuses, weeks, by_id, locale, logo, stamp, commit),
            encoding="utf-8",
        )
        print(f"wrote {path.relative_to(gr.ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
