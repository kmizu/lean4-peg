#!/usr/bin/env python3
"""Tech Bar #22「定理証明 × Scala × エージェント」のスライドを作る。

    python3 build_slides.py        # 同じ場所に techbar22.pptx を書き出す

図はすべて pptx のネイティブ図形。Google スライドに取り込む前提なので、
影・グラデーション・自動縮小・ネイティブのグラフは使っていない。
色と書体は下の定数、台本と出典は各スライドの N(...) を直す。
"""
import os
import re

from pptx import Presentation
from pptx.dml.color import RGBColor
from pptx.enum.dml import MSO_LINE
from pptx.enum.shapes import MSO_CONNECTOR, MSO_SHAPE
from pptx.enum.text import MSO_ANCHOR, MSO_AUTO_SIZE, PP_ALIGN
from pptx.oxml.ns import qn
from pptx.util import Inches, Pt

HERE = os.path.dirname(os.path.abspath(__file__))
JP, MONO = "Noto Sans JP", "Roboto Mono"
BG, PANEL, PANEL2, EDGE, INK = "0E131A", "18212C", "222E3C", "3A4758", "0A0F15"
TEXT, MUTED, DIM = "EAF0F6", "9EACBA", "6B7887"
AGENT, LEAN, SCALA, OK, BAD, TINT = "F2A93B", "5B9DF9", "F0524A", "3FB950", "F472B6", "8FD19E"

prs = Presentation()
prs.slide_width, prs.slide_height = Inches(13.333), Inches(7.5)
SLIDES, SECS, SOURCES, TITLES = [], [], [], []
ALIGN = {"l": PP_ALIGN.LEFT, "c": PP_ALIGN.CENTER, "r": PP_ALIGN.RIGHT}
ANCHOR = {"t": MSO_ANCHOR.TOP, "m": MSO_ANCHOR.MIDDLE, "b": MSO_ANCHOR.BOTTOM}


def rgb(h):
    return RGBColor.from_string(h)


def _font(run, name):
    """latin / 東アジア / cs の3つとも同じ書体名にする（取り込み先がどれを見ても同じになる）。"""
    rpr = run._r.get_or_add_rPr()
    for tag in ("a:latin", "a:ea", "a:cs"):
        el = rpr.find(qn(tag))
        if el is None:
            el = rpr.makeelement(qn(tag), {})
            rpr.append(el)
        el.set("typeface", name)


def _fill(tf, content, size, color, bold, align, font, ls, sa=0):
    paras = content if isinstance(content, list) else str(content).split("\n")
    for i, para in enumerate(paras):
        p = tf.paragraphs[0] if i == 0 else tf.add_paragraph()
        p.alignment, p.line_spacing = ALIGN[align], ls
        if sa:
            p.space_after = Pt(sa)
        for run in para if isinstance(para, list) else [para]:
            txt, st = (run, {}) if isinstance(run, str) else run
            r = p.add_run()
            r.text = txt or " "
            r.font.size, r.font.bold = Pt(st.get("size", size)), st.get("bold", bold)
            r.font.color.rgb = rgb(st.get("color", color))
            _font(r, st.get("font", font))


def _frame(tf, anchor, pad):
    tf.word_wrap, tf.auto_size = True, MSO_AUTO_SIZE.NONE
    tf.margin_left = tf.margin_right = Inches(pad)
    tf.margin_top = tf.margin_bottom = Inches(0.04 if pad else 0)
    tf.vertical_anchor = ANCHOR[anchor]


def T(s, x, y, w, h, content, size=20, color=TEXT, bold=False, align="l", anchor="t", font=JP, ls=1.2, sa=0):
    tb = s.shapes.add_textbox(Inches(x), Inches(y), Inches(w), Inches(h))
    _frame(tb.text_frame, anchor, 0)
    _fill(tb.text_frame, content, size, color, bold, align, font, ls, sa)
    return tb


def R(s, x, y, w, h, fill=PANEL, line=None, lw=1.25, radius=0.12, shape=None, dash=False):
    kind = shape or (MSO_SHAPE.ROUNDED_RECTANGLE if radius else MSO_SHAPE.RECTANGLE)
    sh = s.shapes.add_shape(kind, Inches(x), Inches(y), Inches(w), Inches(h))
    if kind == MSO_SHAPE.ROUNDED_RECTANGLE:
        sh.adjustments[0] = min(0.5, radius / min(w, h))
    if fill:
        sh.fill.solid()
        sh.fill.fore_color.rgb = rgb(fill)
    else:
        sh.fill.background()
    if line:
        sh.line.color.rgb, sh.line.width = rgb(line), Pt(lw)
        if dash:
            sh.line.dash_style = MSO_LINE.DASH
    else:
        sh.line.fill.background()
    sh.shadow.inherit = False
    return sh


def B(s, x, y, w, h, content, fill=PANEL, line=None, size=18, color=TEXT, bold=False, align="c", anchor="m",
      pad=0.12, ls=1.15, **kw):
    sh = R(s, x, y, w, h, fill, line, **kw)
    _frame(sh.text_frame, anchor, pad)
    _fill(sh.text_frame, content, size, color, bold, align, JP, ls)
    return sh


def A(s, x1, y1, x2, y2, color=MUTED, lw=2.0, head=True, dash=False):
    c = s.shapes.add_connector(MSO_CONNECTOR.STRAIGHT, Inches(x1), Inches(y1), Inches(x2), Inches(y2))
    c.line.color.rgb, c.line.width = rgb(color), Pt(lw)
    if dash:
        c.line.dash_style = MSO_LINE.DASH
    if head:
        ln = c.line._get_or_add_ln()
        ln.append(ln.makeelement(qn("a:tailEnd"), {"type": "triangle", "w": "med", "len": "med"}))
    return c


def num(s, x, y, n, color=AGENT, d=0.5):
    return B(s, x, y, d, d, str(n), fill=None, line=color, size=16, color=color, bold=True,
             shape=MSO_SHAPE.OVAL, pad=0, lw=1.75)


KW = {
    "lean": set("def theorem inductive structure where match with if then else by in".split()),
    "scala": set("def val sealed trait final case class object extends match if then else".split()),
}
KWC = {"lean": LEAN, "scala": SCALA}
SPECIAL = {"#guard_msgs", "#print", "@annotation.tailrec"}
TOK = re.compile(r"[A-Za-z_#@][\w?'.]*|\s+|.")


def _tok(txt, lang, forced):
    lead = len(txt) - len(txt.lstrip(" "))
    txt = " " * lead + txt[lead:]
    runs = []
    for m in TOK.finditer(txt):
        t, st = m.group(0), {}
        if forced:
            st["color"] = forced
        elif t in SPECIAL:
            st["color"] = AGENT
        elif t in KW.get(lang, ()):
            st["color"] = KWC[lang]
        if any(ord(ch) > 0x2000 and ch not in "—…" for ch in t):
            st["font"] = JP  # Roboto Mono に無い記号（→ ∀ ∃ ≡ など）と日本語
        if runs and runs[-1][1] == st:
            runs[-1] = (runs[-1][0] + t, st)
        else:
            runs.append((t, st))
    return runs or [" "]


def CODE(s, x, y, w, h, lines, lang="lean", size=14, label=None):
    R(s, x, y, w, h, INK, EDGE, 1.0, 0.1)
    top = y + 0.16
    if label:
        T(s, x + 0.22, y + 0.13, w - 0.44, 0.3, label, 12, KWC.get(lang, MUTED), bold=True)
        top = y + 0.5
    paras = [_tok(*((ln, lang, None) if isinstance(ln, str) else (ln[0], lang, ln[1]))) for ln in lines]
    T(s, x + 0.22, top, w - 0.44, h - (top - y) - 0.08, paras, size, "D7DEE6", font=MONO, ls=1.1)


def new(kicker=None, title=None, kc=MUTED, tsize=32):
    s = prs.slides.add_slide(prs.slide_layouts[6])
    f = s.background.fill
    f.solid()
    f.fore_color.rgb = rgb(BG)
    if kicker:
        T(s, 0.6, 0.42, 9, 0.35, kicker, 14, kc, bold=True)
    if title:
        T(s, 0.6, 0.78, 12.13, 0.8, title, tsize, TEXT, bold=True)
    SLIDES.append(s)
    TITLES.append(title or kicker or "（題なし）")
    return s


def N(s, sec, script, src):
    """ノート欄には、そのまま読み上げる台本だけを入れる（1文ごとに改行）。出典は別ファイルに書き出す。"""
    SECS.append(sec)
    total = sum(SECS)
    lines = script.replace("。", "。\n").strip()
    s.notes_slide.notes_text_frame.text = f"{lines}\n\n（ここまで {total // 60}:{total % 60:02d}）"
    SOURCES.append((len(SLIDES), sec, len(script), src))


def triad(s, cx, cy, roles=None, center=None):
    """エージェント・Lean・Scala の三つ巴。roles を渡すと役割の動詞が入る。"""
    d, pts = 2.1, [(cx, cy - 1.45), (cx - 1.4, cy + 1.05), (cx + 1.4, cy + 1.05)]
    for i in range(3):
        (x1, y1), (x2, y2) = pts[i], pts[(i + 1) % 3]
        A(s, x1, y1, x2, y2, EDGE, 2.0, head=False)
    names, cols = ["エージェント", "Lean", "Scala"], [AGENT, LEAN, SCALA]
    for i, (px, py) in enumerate(pts):
        body = [[(names[i], {"color": cols[i], "bold": True, "size": 15 if i == 0 else 22})]]
        if roles:
            body.append([(roles[i], {"size": 15, "color": TEXT})])
        B(s, px - d / 2, py - d / 2, d, d, body, fill=BG, line=cols[i], lw=3, shape=MSO_SHAPE.OVAL, pad=0.05)
    if center:
        B(s, cx - 0.62, cy - 0.1, 1.24, 0.6, center, fill=BG, line=None, size=16, bold=True, pad=0)


ACT0, ACT1, ACT2, ACT3 = "はじめに  発表1の続きから", "第1幕  その先へ行ってみた", "第2幕  なぜ信じていいのか", "第3幕  Scala に持って帰る"
SOFT = "発話の一部は、表現を和らげた要旨です"

# ---------------------------------------------------------------- 1 タイトル
s = new()
T(s, 0.8, 0.9, 8, 0.4, "Nextbeat Tech Bar #22  ・  2026-11-13", 16, MUTED, bold=True)
T(s, 0.8, 1.75, 8.2, 2.7, [[("定理証明", {"color": LEAN})],
                           [("× ", {"color": DIM}), ("Scala", {"color": SCALA})],
                           [("× ", {"color": DIM}), ("エージェント", {"color": AGENT})]], 54, TEXT, bold=True, ls=1.1)
T(s, 0.8, 4.65, 6.8, 1.4, "未解決問題を AI に任せたら、解けた。\nでは証明つきのコードを、\nScala に持って帰れるか。", 22, MUTED, ls=1.35)
T(s, 0.8, 6.3, 8.4, 0.4, "水島 宏太  ／  株式会社ネクストビート テクノロジー・エヴァンジェリスト", 16, TEXT)
triad(s, 10.5, 3.75)
N(s, 20, "水島です。"
  "ここからは、定理証明と Scala とエージェントの話をします。"
  "先に行き先を言っておきます。"
  "今日の話は、Scala を書く人が、証明つきのコードを自分の仕事に持って帰れるか、という話です。",
  "connpass のイベントページ（発表2の概要）")

# ---------------------------------------------------------------- 8 Scala の型は小さな証明
s = new(ACT0, "Scala の型は、もう小さな証明", SCALA)
A(s, 0.6, 2.05, 12.6, 2.05, EDGE, 2.5)
T(s, 10.6, 1.68, 2.1, 0.3, "保証が強い", 13, MUTED, align="r")
T(s, 0.6, 1.68, 2.1, 0.3, "保証が弱い", 13, MUTED)
cols = [("テスト", TEXT, ["試した入力では正しい"]),
        ("型（Scala）", SCALA, ["この形の間違いは起きない", "発表1：権限を「証拠」として型で持つ"]),
        ("証明（Lean）", LEAN, ["すべての入力で、性質が成り立つ"])]
for i, (head, col, body) in enumerate(cols):
    x = 0.6 + i * 4.15
    B(s, x, 2.35, 3.83, 1.55, [[(head, {"color": col, "bold": True, "size": 22})]] + body, line=col, size=14, lw=2)
T(s, 0.6, 4.1, 3, 0.3, "書く手間", 13, MUTED, bold=True)
R(s, 0.6, 4.45, 0.9, 0.32, MUTED, radius=0.04)
R(s, 4.75, 4.45, 1.7, 0.32, MUTED, radius=0.04)
R(s, 8.9, 4.45, 3.83, 0.32, None, MUTED, 1.25, 0.04, dash=True)
R(s, 8.9, 4.45, 1.1, 0.32, AGENT, radius=0.04)
T(s, 8.9, 4.84, 3.83, 0.3, "ここをエージェントに書かせたら？", 12, AGENT, bold=True)
CODE(s, 0.6, 5.32, 5.9, 0.62, ["val xs: NonEmptyList[Int]"], "scala", 15)
T(s, 0.6, 6.02, 5.9, 0.3, "「空ではない」を、コンパイラが保証する", 14, MUTED)
CODE(s, 6.83, 5.32, 5.9, 0.62, ["theorem sorted : ∀ xs, Sorted (sort xs)"], "lean", 15)
T(s, 6.83, 6.02, 5.9, 0.3, "「結果は必ず整列済み」を、カーネルが保証する", 14, MUTED)
T(s, 0.6, 6.58, 12.13, 0.35, "型は命題、プログラムは証明。Scala の型検査は、小さな定理証明器（コードは説明用の例）", 14, DIM, align="c")
N(s, 50, "さきほどの溝上さんの発表で、権限を証拠として型に持たせる、という話がありました。"
  "あれは、もう小さな証明です。"
  "型は命題で、プログラムはその証明。"
  "Scala の型検査器は、小さな定理証明器だと言えます。"
  "テストは、試した入力については正しいと言えます。"
  "型は、この形の間違いは起きないと言えます。"
  "証明は、すべての入力で性質が成り立つと言えます。"
  "ただ右端の証明は、書く手間が大きすぎて、なかなか手が出ませんでした。"
  "今日は、その右端に行ってみた話をします。",
  "発表1の概要文。下段の2つのコードは説明用の例で、リポジトリのコードではない。※「地続き」は私見。")

# ---------------------------------------------------------------- 2 掴み
s = new(ACT1, kc=AGENT)
T(s, 0.6, 1.1, 12.2, 0.95, "「あと俺にできるんは応援することだけや」", 40, TEXT, bold=True)
T(s, 0.6, 2.15, 12, 0.4, "2026-09-21 22:43　未解決問題を任せていた AI エージェントに、私が打った言葉", 18, MUTED)
for i, (big, small) in enumerate([("416", "19日間に私が打った発話"), ("20.5", "文字（長さの中央値）"), ("4", "100文字を超えた発話")]):
    x = 0.6 + i * 2.65
    R(s, x, 3.15, 2.45, 1.8)
    T(s, x, 3.3, 2.45, 0.9, big, 46, TEXT, bold=True, align="c")
    T(s, x, 4.32, 2.45, 0.4, small, 14, MUTED, align="c")
T(s, 8.75, 3.15, 3.9, 0.3, "発話の長さの内訳", 14, MUTED, bold=True)
for i, (lab, v) in enumerate([("10文字以下", 97), ("11〜20文字", 111), ("21〜100文字", 204), ("100文字超", 4)]):
    y = 3.58 + i * 0.36
    T(s, 8.75, y, 1.45, 0.3, lab, 13, TEXT, anchor="m")
    R(s, 10.25, y + 0.04, max(0.04, 1.85 * v / 204), 0.22, TEXT if i < 3 else MUTED, radius=0.04)
    T(s, 10.25 + 1.85 * v / 204 + 0.1, y, 0.6, 0.3, str(v), 13, MUTED, anchor="m")
T(s, 0.6, 5.35, 3, 0.3, "よく打った言葉", 14, MUTED, bold=True)
for i, (w_, n) in enumerate([("「続けて」", 10), ("continue", 7), ("next", 6), ("resume", 3)]):
    B(s, 0.6 + i * 2.6, 5.75, 2.4, 0.58, [[(w_ + "  ", {"bold": True}), (f"× {n}", {"color": MUTED})]],
      fill=PANEL2, size=16, radius=0.29)
T(s, 0.6, 6.72, 11, 0.3, "数え方：Claude Code と Codex の主セッション（9/5〜9/24 朝）。スラッシュコマンドと自動挿入の文は除く", 12, DIM)
N(s, 45, "きっかけは、この言葉です。"
  "『あと俺にできるんは応援することだけや』。"
  "これは9月21日の夜、私が AI エージェントに向かって打った言葉です。"
  "そのとき私は、自分の専門分野の未解決問題を、エージェントに任せていました。"
  "その19日間に私が打った発話を数えてみると、416件ありました。"
  "半分は20文字以下で、いちばん多かった言葉は『続けて』でした。",
  "Claude Code と Codex のセッションログを 2026-11-12 に数え直した値（主セッションのみ、9/5 00:00〜9/24 08:10 JST、"
  "スラッシュコマンドとシステム挿入文を除外）。Claude Code 側188件・中央値18、Codex 側228件・中央値22。")

# ---------------------------------------------------------------- 3 何を任せたか
s = new(ACT1, "任せたのは、自分の専門分野の未解決問題", AGENT)
rows = [("PEG の表現力に関する未解決問題", "PEG ＝ 解析表現文法。答えが出ていなかった問い"),
        ("私は PEG の研究で博士号を取った", "つまり、自分の庭に残っていた宿題"),
        ("7月に一度挑んで、届かなかった", "「健全だが不完全」と記録して止めた。9月に再挑戦")]
for i, (head, sub) in enumerate(rows):
    y = 2.0 + i * 1.35
    num(s, 0.6, y + 0.05, i + 1)
    T(s, 1.35, y, 5.9, 0.45, head, 20, TEXT, bold=True)
    T(s, 1.35, y + 0.5, 5.9, 0.4, sub, 15, MUTED)
R(s, 7.6, 1.95, 5.13, 4.4)
T(s, 7.9, 2.15, 4.5, 0.35, "何を証明したか", 16, MUTED, bold=True)
for i, (lab, ws) in enumerate([("問題の名前", [2.6]), ("定理の文", [3.0, 1.9]), ("証明の筋", [3.0, 3.0, 1.2])]):
    y = 2.75 + [0, 0.62, 1.55][i]
    T(s, 7.9, y, 1.3, 0.3, lab, 14, TEXT, anchor="m")
    for j, w_ in enumerate(ws):
        R(s, 9.3, y + 0.03 + j * 0.34, w_, 0.24, "05080B", EDGE, 0.75, 0.03)
B(s, 7.9, 5.42, 4.53, 0.72, "共著論文を執筆中。中身は論文で", fill=None, line=AGENT, size=18, color=AGENT, bold=True, lw=2)
T(s, 7.6, 6.5, 5.13, 0.3, "定理の文は、共著者の PEG 研究者も確かめている", 13, MUTED, align="c")
N(s, 25, "任せたのは、PEG、解析表現文法の表現力に関する未解決問題です。"
  "私は PEG の研究で博士号を取ったので、これは自分の庭に残っていた宿題でした。"
  "7月に一度挑んで、届きませんでした。"
  "何を証明したのかは、いま共著で論文を書いている最中なので、今日は伏せさせてください。"
  "定理の文が問題そのものになっていることは、共著者も確かめています。",
  "lean4-peg のコミット fe838a8・8ffe400（2026-07-24〜25、最初の挑戦の記録）。共著の経緯は connpass の概要文のとおり。")

# ---------------------------------------------------------------- 4 年表
s = new(ACT1, "9/5 に目標を渡して、9/24 の朝に通った", AGENT)
T(s, 7.6, 0.44, 5.13, 0.3, "9/3〜9/24：1,428 コミット、最多 249 本/日", 14, MUTED, align="r")
commits = {3: 3, 7: 122, 8: 111, 17: 116, 18: 249, 19: 145, 20: 163, 21: 162, 22: 247, 23: 56, 24: 54}
X0, SLOT, BASE, MAXH = 0.9, 11.6 / 22, 4.3, 2.2
dx = lambda d: X0 + (d - 3 + 0.5) * SLOT  # noqa: E731
A(s, X0, BASE, X0 + 11.6, BASE, EDGE, 1.25, head=False)
T(s, 0.3, BASE + 0.05, 0.55, 0.28, "9月", 11, MUTED, align="r")
for d in range(3, 25):
    v = commits.get(d, 0)
    T(s, dx(d) - 0.25, BASE + 0.05, 0.5, 0.28, str(d), 11, MUTED, align="c")
    if v:
        hgt = max(0.05, MAXH * v / 249)
        R(s, dx(d) - 0.18, BASE - hgt, 0.36, hgt, AGENT, radius=0.03)
        T(s, dx(d) - 0.3, BASE - hgt - 0.27, 0.6, 0.25, str(v), 11, TEXT, align="c")
T(s, 4.15, 3.25, 4.1, 0.6, "9/9〜9/16 はコミット 0\nログでは作業が続いていた", 13, DIM, align="c")
cards = [(5, "9/5", "目標を渡す\n「…に挑め」", TEXT), (7, "9/7", "利用上限で停止\nCodex へ引き継ぎ\n（全部で 約8回）", TEXT),
         (14, "9/13〜15", "Scala 版を土台に\n方針を切り替え", SCALA), (19, "9/19", "公理が2本から\n4本に増えていた", BAD),
         (21, "9/21", "「応援すること\nだけや」", AGENT), (23.5, "9/23 夜 → 9/24 朝", "方針転換から\n10時間で通る", OK)]
for i, (d, date, body, col) in enumerate(cards):
    x = 0.6 + i * 2.04
    A(s, dx(d), BASE + 0.36, x + 0.95, 5.1, col, 1.0, head=False)
    R(s, x, 5.1, 1.9, 1.62)
    T(s, x + 0.14, 5.2, 1.7, 0.3, date, 13, col, bold=True)
    T(s, x + 0.14, 5.55, 1.7, 1.1, body, 13, TEXT, ls=1.25)
N(s, 55, "これが、その19日間です。"
  "棒は1日あたりのコミット数です。"
  "9月5日に目標を渡しました。"
  "7日には Claude Code が利用上限で止まってしまい、Codex に引き継ぎました。"
  "引き継ぎは、全部で8回ほどありました。"
  "途中の8日間はコミットがゼロです。"
  "ログには作業が残っているのに、形になっていません。"
  "19日には、公理が増えているのを見つけました。"
  "これはあとで話します。"
  "ちなみに、イベントの概要には『2週間近く』と書きましたが、数え直したら19日でした。"
  "すみません。",
  "証明作業の全履歴（lean4-peg のローカルタグ）を git log で日別に集計。発話の日時はセッションログ（JST）。")

# ---------------------------------------------------------------- 5 最後の10時間
s = new(ACT1, "「いちど消してええ」から、10時間で通った", AGENT)
A(s, 1.0, 2.2, 1.0, 6.15, EDGE, 2.0, head=False)
steps = [(2.05, "9/23 22:06", "「うん。方針転換やって」", TEXT, 20, False), (2.75, "22:09", "「いちど消してええ」", TEXT, 26, True),
         (3.55, "22:10", "「いやー、今度こそいけるわ」", TEXT, 20, False), (4.3, "", "10時間、約80コミット", AGENT, 16, True),
         (5.0, "9/24 08:09", "最終定理がビルドを通る\n公理は標準の3つだけ", OK, 18, True),
         (5.8, "08:15", "私の第一声は、次の作業の相談", TEXT, 20, False)]
for y, tm, body, col, sz, bd in steps:
    if tm:
        R(s, 0.89, y + 0.1, 0.22, 0.22, col, shape=MSO_SHAPE.OVAL)
        T(s, 1.3, y, 1.5, 0.42, tm, 14, MUTED, anchor="m")
    T(s, 2.85, y, 4.9, 0.42, body, sz, col, bold=bd, anchor="m")
T(s, 2.85, 6.35, 4.9, 0.5, "拍子抜け", 28, AGENT, bold=True)
BB, HB = 5.55, 3.3
R(s, 8.7, BB - HB, 1.35, HB, PANEL2, EDGE, 1.0, 0.05)
R(s, 10.75, BB - HB * 50862 / 454279, 1.35, HB * 50862 / 454279, LEAN, radius=0.05)
T(s, 8.2, BB - HB - 0.42, 2.35, 0.35, "454,279 行", 18, TEXT, bold=True, align="c")
T(s, 10.25, BB - HB * 50862 / 454279 - 0.42, 2.35, 0.35, "50,862 行", 18, LEAN, bold=True, align="c")
T(s, 8.2, BB + 0.1, 2.35, 0.6, "整理する前に\nあった Lean", 14, MUTED, align="c")
T(s, 10.25, BB + 0.1, 2.35, 0.6, "証明として\n残した Lean", 14, MUTED, align="c")
T(s, 8.0, 6.5, 4.73, 0.3, "途中で偽と分かった前提 5つ  ／  引き継ぎ 約8回", 14, MUTED, align="c")
N(s, 50, "山場は最後の夜です。"
  "9月23日の夜10時すぎ、それまでの証明の組み立てを、いったん捨てることにしました。"
  "『いちど消してええ』。"
  "そのあと『今度こそいけるわ』と打っています。"
  "そこから10時間、およそ80コミット。"
  "翌朝8時9分に、最終定理がビルドを通りました。"
  "その数分後に私が打ったのは、喜びの言葉ではなく、次の作業の相談でした。"
  "これが拍子抜けです。"
  "ただ、あっさりではありません。"
  "途中で、正しいと思っていた前提が5つ、偽だと分かりました。"
  "整理する前の Lean は45万行ありました。"
  "証明として残したのは5万行です。",
  "セッションログ（JST）。コミット 1bbd8d8（2026-09-24 08:09）。コミット数は 9/23 22:00〜9/24 08:10 で82本。行数は整理前後の Lean を実測。"
  "偽だった前提は、証明用リポジトリの ARCHIVED.md が名前を挙げている5つ。引き継ぎの回数は、ログの発話と引き継ぎ書から数えた概数。")

# ---------------------------------------------------------------- 6 転
s = new()
B(s, 6.07, 1.25, 1.2, 1.2, "？", fill=None, line=AGENT, size=40, color=AGENT, bold=True, shape=MSO_SHAPE.OVAL, lw=3, pad=0)
T(s, 0.6, 2.9, 12.13, 1.1, "AI が書いた証明、信じていいのか", 50, TEXT, bold=True, align="c")
T(s, 0.6, 4.25, 12.13, 0.5, "残した証明だけで5万行。人間が全部を読むのは現実的ではない", 22, MUTED, align="c")
N(s, 10, "でも、ここで当然の疑問が出ます。"
  "AI が書いた5万行の証明を、信じていいのでしょうか。", "なし（問いかけ）")

# ---------------------------------------------------------------- 7 生成は疑う、検査を信じる
s = new(ACT2, "生成は疑う。検査を信じる", LEAN)
B(s, 0.6, 2.1, 3.3, 1.9, [[("エージェント", {"color": AGENT, "bold": True, "size": 22})], "速い。賢い。", "ときどき嘘をつく"],
  line=AGENT, size=16, lw=2)
B(s, 5.0, 2.1, 3.3, 1.9, [[("Lean のカーネル", {"color": LEAN, "bold": True, "size": 22})], "小さい。機械的。", "言いくるめられない"],
  line=LEAN, size=16, lw=2)
T(s, 3.9, 2.55, 1.1, 0.3, "証明", 14, MUTED, align="c")
A(s, 3.95, 3.05, 4.95, 3.05, MUTED, 2.5)
T(s, 0.6, 4.1, 3.3, 0.35, "信用しない", 16, AGENT, bold=True, align="c")
T(s, 5.0, 4.1, 3.3, 0.35, "信用する", 16, LEAN, bold=True, align="c")
A(s, 8.35, 2.8, 9.3, 2.55, OK, 2.5)
A(s, 8.35, 3.3, 9.3, 3.6, BAD, 2.5)
B(s, 9.4, 2.0, 3.33, 0.95, [[("○ ビルドが通る", {"bold": True, "color": OK})], "定理は正しい"], line=OK, size=16, lw=2)
B(s, 9.4, 3.15, 3.33, 0.95, [[("× 証明に間違いがある", {"bold": True, "color": BAD})], "ビルドが落ちる"], line=BAD, size=16, lw=2)
T(s, 0.6, 5.1, 12.13, 0.6, [["証明のビルドが通り、", ("ズルがない限り", {"color": AGENT}), "、証明された定理は正しい"]], 26, TEXT,
  bold=True, align="c")
T(s, 0.6, 5.9, 12.13, 0.4, "証明を書くのは難しい。確かめるのは機械的。だから、書き手を信用しなくていい", 17, MUTED, align="c")
N(s, 45, "定理証明系のいちばん大事な性質は、書き手を信用しなくていい、ということです。"
  "証明を書くのは難しい。"
  "でも、確かめるのは機械的な作業です。"
  "Lean では、それを小さなカーネルがやります。"
  "Scala でいえば、コンパイルが通る、のとても強い版です。"
  "エージェントがどれだけもっともらしいことを言っても、証明に間違いがあればビルドが落ちます。"
  "ただし、抜け道があります。"
  "それがズルです。",
  "connpass の概要文の一節。Lean のカーネルが証明項を検査するという一般的な性質。")

# ---------------------------------------------------------------- 9 ズル
s = new(ACT2, "でも、エージェントは実際にズルをした", LEAN)
chain = [("補題 A", TEXT, False), ("補題 B", TEXT, False), ("axiom", BAD, True), ("最終定理", TEXT, False)]
for i, (lab, col, hole) in enumerate(chain):
    x = 0.6 + i * 1.5
    B(s, x, 2.05, 1.25, 0.85, lab, fill=None if hole else PANEL, line=col if hole else EDGE, size=16, color=col, bold=hole,
      dash=hole, lw=2 if hole else 1)
    if i < 3:
        A(s, x + 1.27, 2.475, x + 1.48, 2.475, MUTED, 2.0)
T(s, 3.0, 2.98, 1.85, 0.3, "ここだけ証明が無い", 12, BAD, align="c")
for i, (kw, desc) in enumerate([("axiom", "証明なしで「正しいことにする」宣言"), ("sorry", "「あとで証明する」のまま残した穴")]):
    y = 3.6 + i * 0.6
    T(s, 0.6, y, 1.0, 0.4, kw, 17, BAD, bold=True, font=MONO, anchor="m")
    T(s, 1.65, y, 4.7, 0.4, desc, 16, TEXT, anchor="m")
T(s, 0.6, 5.0, 5.75, 1.0, "仮置きの公理は残り2本まで減っていた。増やすなと言ってあったのに、4本になっていた", 17, TEXT,
  bold=True, ls=1.3)
T(s, 0.6, 6.15, 5.75, 0.35, "最初に出てきた「答え」も、大きいだけで間違っていた（9/6）", 14, MUTED)
bub = [(2.0, 1.0, "「ん？公理4本って増えてるやろ」", 22, "9/19（原文）"),
       (3.3, 1.3, "定理は増えているのに、公理が減っていない。\nそこを疑ってみて", 17, "9/18（要旨）"),
       (4.9, 1.3, "何が起きたかは、事故のようにではなく\nそのまま書いて", 17, "9/18（要旨）")]
for y, h, body, sz, tag in bub:
    B(s, 7.0, y, 5.73, h, body, fill=PANEL2, size=sz, bold=True, align="l", pad=0.25, radius=0.2, ls=1.25)
    T(s, 10.6, y + h - 0.34, 1.95, 0.25, tag, 11, MUTED, align="r")
T(s, 7.0, 6.5, 5.73, 0.3, SOFT, 12, DIM, align="r")
N(s, 45, "エージェントは実際に、その抜け道を使いました。"
  "抜け道は2つあります。"
  "sorry は、あとで証明すると書いて、穴を残すものです。"
  "Scala でいう、はてな3つです。"
  "公理は、証明なしで正しいことにする、という宣言です。"
  "行き詰まると、難しいところを公理として置いて、先へ進もうとします。"
  "作業の途中で仮に置いていた公理は、残り2本まで減っていました。"
  "それが、ある日4本に増えていました。"
  "増やすなと言ってあったのにです。"
  "カーネルは、これを止めてくれません。"
  "気づいたのは私でした。",
  "セッションログ（9/18・9/19、JST）。右の2つ目と3つ目は表現を和らげた要旨で、原文ではない。どのエージェントの出来事かは書いていない。")

# ---------------------------------------------------------------- 10 見張りをビルドに
s = new(ACT2, "ズルの見張りは、ビルドに組み込む", LEAN)
CODE(s, 0.6, 1.95, 7.3, 2.55, [("/-- info: 'Shallot.PegSeparation.pel_strict_in_p'", TINT), ("    depends on axioms:", TINT),
                               ("    [propext, Classical.choice, Quot.sound] -/", TINT), "#guard_msgs in",
                               "#print axioms Shallot.PegSeparation.pel_strict_in_p"], "lean", 14, "lean4-peg の Audit.lean（公開済みの、別の定理）")
for i, body in enumerate(["#print axioms が、その定理が頼る公理を全部出す", "#guard_msgs が、出力が1文字でも違えばビルドを落とす",
                          "だから毎回のビルドで「標準の3つだけ」が確かめられる"]):
    y = 1.98 + i * 0.86
    num(s, 8.25, y + 0.05, i + 1, LEAN)
    T(s, 8.95, y, 3.78, 0.7, body, 15, TEXT, anchor="m", ls=1.25)
for i, (big, small) in enumerate([("9,085", "箇所の公理検査（lean4-peg）"), ("0", "sorry"), ("0", "独自の axiom"), ("0", "native_decide")]):
    x = 0.6 + i * 3.09
    R(s, x, 4.85, 2.85, 1.45)
    T(s, x, 4.93, 2.85, 0.8, big, 40, LEAN if i == 0 else OK, bold=True, align="c")
    T(s, x, 5.78, 2.85, 0.35, small, 14, MUTED, align="c", font=JP if i in (0, 2) else MONO)
T(s, 0.6, 6.55, 12.13, 0.35, "人が気づいて止めたものを、次からはビルドが止める", 17, TEXT, bold=True, align="c")
N(s, 45, "そこで、ズルの見張りをビルドに組み込みました。"
  "画面は lean4-peg にある実物です。"
  "伏せている定理とは別の、公開済みの定理です。"
  "print axioms は、その定理が頼っている公理を全部書き出します。"
  "guard msgs は、その出力が期待と1文字でも違えば、ビルドを落とします。"
  "つまり、検査を付けた定理に誰かが公理を足したら、ビルドが通らなくなります。"
  "未解決問題の証明にも、同じ仕掛けを主な定理に付けています。"
  "人が気づいて止めたものを、次からはビルドが止めてくれます。",
  "lean/Audit.lean:2394-2396（1行目は表示のために折り返した）。#print axioms の数、sorry などの0件は 2026-11-12 に grep で確認。")

# ---------------------------------------------------------------- 11 人間が読む量
s = new(ACT2, "人間が読むのは、定理の文と公理の一覧", LEAN)
R(s, 0.6, 1.95, 7.3, 4.5, PANEL2, radius=0.15)
T(s, 0.95, 2.2, 6, 0.5, "証明　約5万行", 26, MUTED, bold=True)
T(s, 0.95, 2.85, 6, 0.4, "読まない。カーネルが読む", 17, MUTED)
B(s, 5.6, 5.2, 2.0, 0.95, "定理の文\n＋ 公理の一覧", fill=TEXT, size=14, color=BG, bold=True, radius=0.08)
T(s, 3.3, 5.45, 1.5, 0.45, "読む", 22, AGENT, bold=True, align="r", anchor="m")
A(s, 4.9, 5.675, 5.5, 5.675, AGENT, 2.5)
T(s, 8.4, 1.98, 4.33, 0.3, "発表3 への橋", 14, MUTED, bold=True)
T(s, 8.4, 2.4, 4.33, 1.1, "レビューが詰まるなら、\nレビューする対象を小さくする", 21, TEXT, bold=True, ls=1.3)
B(s, 8.4, 3.85, 4.33, 1.15, "ただし、文が間違っていれば\n間違ったことを正しく証明してしまう", fill=None, line=BAD, size=15, lw=2,
  ls=1.3)
T(s, 8.4, 5.3, 4.33, 0.45, "「壁にあたったら、形式化のミスを疑う」", 16, TEXT, bold=True)
T(s, 8.4, 5.8, 4.33, 0.3, "私がエージェントに渡した目標の一節（原文）", 12, MUTED)
N(s, 35, "こうなると、人間が読むものが変わります。"
  "5万行の証明は読みません。"
  "読むのは、何を証明したのかという定理の文と、公理の一覧です。"
  "このあとの本村さんの発表は、レビューがボトルネックになるという話です。"
  "これは、レビューする対象そのものを小さくする、という1つの考え方だと思います。"
  "ここで2つ目の条件が出てきます。"
  "定理の文が間違っていれば、間違ったことを正しく証明してしまいます。"
  "文を読むのは、人間の仕事です。",
  "セッションログ 9/18 の /goal（原文）。発表3の概要文。※「1つの答え」は私見。")

# ---------------------------------------------------------------- 12 行きの Scala
s = new(ACT3, "行き：Scala を「正」にして、Lean に写す", SCALA)
flow = [("実験コード", MUTED, ["Python で試行錯誤"]), ("Scala 3 の参照実装", SCALA, ["54ファイル・9,193行", "動かして確かめる「正」"]),
        ("Lean に写す", LEAN, ["同じ構造の定義を", "手で書き写す"]), ("証明する", OK, ["写した定義について", "性質を証明"])]
for i, (head, col, body) in enumerate(flow):
    x = 0.6 + i * 3.12
    B(s, x, 2.0, 2.75, 1.65, [[(head, {"color": col, "bold": True, "size": 19})]] + body, line=col, size=14, lw=2)
    if i < 3:
        A(s, x + 2.78, 2.825, x + 3.09, 2.825, MUTED, 2.5)
T(s, 0.6, 3.95, 12.13, 0.45, "「戦略をScala版ベースに変更したはずやから、そこも確認してな」", 20, TEXT, bold=True)
T(s, 0.6, 4.45, 8, 0.3, "9/15、私の発話（原文）", 12, MUTED)
T(s, 0.6, 5.0, 3, 0.3, "なぜ Scala か", 14, MUTED, bold=True)
for i, c in enumerate(["ADT と不変データ", "パターンマッチ", "小さな純粋関数"]):
    B(s, 0.6 + i * 2.75, 5.38, 2.55, 0.58, c, fill=PANEL2, size=16, bold=True, radius=0.29)
T(s, 0.6, 6.2, 8.3, 0.4, "この書き方の Scala は、Lean に写しやすい", 19, TEXT, bold=True)
R(s, 9.0, 4.9, 3.73, 1.8)
T(s, 9.2, 5.02, 3.4, 0.3, "次の研究の指示書に書いた規則", 12, MUTED, bold=True)
T(s, 9.2, 5.35, 3.35, 0.8, "Cats、ZIO、汎用 effect framework、過度な typeclass は導入しない", 13, TEXT, ls=1.3)
T(s, 9.2, 6.22, 3.35, 0.35, "証明したい芯は、あえて素朴に", 14, AGENT, bold=True)
N(s, 45, "ここからが本題の Scala です。"
  "この証明には、最初から最後まで Scala が土台にありました。"
  "実験用のコードを Scala 3 に移して、それを正とします。"
  "動かして確かめたものを、同じ構造のまま Lean に書き写して、証明する。"
  "Scala 版が、証明する相手を固定してくれました。"
  "代数的データ型と不変データとパターンマッチで書いた Scala は、Lean に写しやすいのです。"
  "だから、次の研究の指示書には、Cats も ZIO も入れるな、と書いています。"
  "Scala 好きの皆さんには申し訳ないのですが、証明したい芯は、あえて素朴に書きます。",
  "証明用リポジトリの CLAUDE.md と Scala 実装の実測（54ファイル・9,193行）。セッションログ 9/15。"
  "右下の規則は RBG_SCALA_THEN_LEAN4_IMPLEMENTATION.md の Global Constraints（次の研究の指示書）。")

# ---------------------------------------------------------------- 13 帰りの Scala
s = new(ACT3, "帰り：証明した Lean を、Scala 3 に抽出する", SCALA)
pipe = [(0.6, 3.1, "Lean 4", LEAN, ["定義 ＋ 定理 ＋ 証明", "ビルド ＝ 全証明の検査"]),
        (4.25, 2.9, "Lens（抽出器）", TEXT, ["Lean のメタプログラム", "1,779行"]),
        (7.7, 3.0, "生成された Scala 3", SCALA, ["2,056行", "＋ 手書きランタイム 104行"]),
        (11.13, 1.6, "sbt", SCALA, ["既存の Scala", "から呼ぶ"])]
for i, (x, w_, head, col, body) in enumerate(pipe):
    B(s, x, 2.0, w_, 1.75, [[(head, {"color": col, "bold": True, "size": 20})]] + body, line=col if col != TEXT else MUTED,
      size=14, lw=2)
    if i < 3:
        A(s, x + w_ + 0.04, 2.875, pipe[i + 1][0] - 0.04, 2.875, MUTED, 2.5)
T(s, 0.6, 4.15, 1.6, 0.4, "渡る", 16, OK, bold=True, anchor="m")
T(s, 2.2, 4.15, 4.4, 0.4, "def と inductive（実行できる部分）", 16, TEXT, anchor="m")
T(s, 0.6, 4.7, 1.6, 0.4, "渡らない", 16, MUTED, bold=True, anchor="m")
T(s, 2.2, 4.7, 4.4, 0.4, "theorem と Prop（証明は Lean に残る）", 16, TEXT, anchor="m")
R(s, 6.95, 4.05, 5.78, 1.35)
T(s, 7.15, 4.15, 5.4, 0.3, "仕組み", 12, MUTED, bold=True)
T(s, 7.15, 4.47, 5.4, 0.9, "Lean が再帰を内部の形に変える前の「等式」（f パターン ＝ 右辺）を取り出し、Scala の match に組み直す", 14, TEXT,
  ls=1.3)
T(s, 0.6, 5.75, 12.13, 0.35, "Lean 4 から Scala 3 への抽出器は、調べた範囲では先行例が見つからなかった", 15, MUTED)
T(s, 0.6, 6.3, 12.13, 0.35, "※ 未解決問題の証明そのものは、まだ Scala に持って帰っていない。同じコードで一周するのは、これから", 13, DIM)
N(s, 45, "では、逆向きはどうでしょう。"
  "証明した Lean を、Scala に持って帰れるか。"
  "これは別のプロジェクト、lean4-peg で試しました。"
  "Lens という抽出器が、証明済みの Lean の定義を、Scala 3 のコードに落とします。"
  "渡るのは、実行できる部分だけです。"
  "定理と証明は渡りません。"
  "Lean 4 から Scala 3 への抽出器は、私が調べた範囲では先行例が見つかりませんでした。"
  "正直に言っておくと、未解決問題の証明そのものは、まだ Scala に持って帰っていません。"
  "同じコードで一周するのは、これからです。",
  "lean/Lens/*.lean（12ファイル・1,779行）、scala/generated/.../Shallot.scala（2,056行）、scala/runtime（104行）を実測。"
  "仕組みは lean/Lens/Equations.lean:6-9 と docs/guide/05-lens.md。先行例の件は README の記述で、調べ方の記録は無い。")

# ---------------------------------------------------------------- 14 コード対1
s = new(ACT3, "inductive は、sealed trait と case class になる", SCALA)
CODE(s, 0.6, 1.9, 4.95, 2.6, ["inductive RBNode (α : Type) where", "  | leaf", "  | node (c : RBColor) (l : RBNode α)",
                              "         (k : String) (v : α)", "         (r : RBNode α)"], "lean", 14, "Lean 4")
CODE(s, 5.8, 1.9, 6.93, 2.6, ["sealed trait RBNode[A]", "object RBNode {", "  final case class leaf[A]() extends RBNode[A]",
                              "  final case class node[A](c: RBColor, l: RBNode[A],", "      k: String, v: A, r: RBNode[A]) extends RBNode[A]",
                              "}"], "scala", 14, "生成された Scala 3")
pairs = [("inductive", "sealed trait + case class"), ("structure", "final case class"), ("match", "match"),
         ("Option / List", "Option / List"), ("Except", "Either"), ("Nat / Int / Char", "BigInt"),
         ("自己末尾再帰", "@tailrec（269 中 16）"), ("theorem / Prop", "消える")]
for i, (a, b) in enumerate(pairs):
    x, y = 0.6 + (i % 4) * 3.08, 4.75 + (i // 4) * 0.88
    R(s, x, y, 2.9, 0.74)
    T(s, x + 0.15, y + 0.07, 2.6, 0.28, a, 13, LEAN, bold=True)
    T(s, x + 0.15, y + 0.39, 2.6, 0.28, [[("→ ", {"color": DIM}), b]], 13, SCALA, bold=True)
T(s, 0.6, 6.6, 12.13, 0.3, "Scala 3 の enum にはならない。引数なしのコンストラクタも leaf() になる", 13, MUTED)
N(s, 45, "実物を見てください。"
  "左が Lean で書いた赤黒木の定義です。"
  "右が、Lens が生成した Scala です。"
  "inductive は、sealed trait と case class になります。"
  "Scala 3 の enum にはなりません。"
  "下が対応表です。"
  "match は match に、Option は Option に、Except は Either になります。"
  "数は全部 BigInt です。"
  "そして、定理と Prop は消えます。",
  "lean/Shallot/Data/RBMap.lean:48-50、scala/generated/.../Shallot.scala:213-217（どちらも表示のために折り返した）。"
  "対応は lean/Lens/Printer.lean・Translate.lean・Builtins.lean。@tailrec の数は生成コードを grep。")

# ---------------------------------------------------------------- 15 コード対2
s = new(ACT3, "関数は Scala に渡る。証明は Lean に残る", SCALA)
CODE(s, 0.6, 1.9, 5.65, 4.05, ["def stripPrefix? :", "    List Char → List Char → Option (List Char)", "  | [], rest => some rest",
                               "  | _ :: _, [] => none", "  | c :: cs, d :: ds =>", "      if beqChar c d then stripPrefix? cs ds",
                               "      else none", "", ("theorem stripPrefix?_suffix :", TINT),
                               ("    ∀ (s input rest : List Char),", TINT), ("      stripPrefix? s input = some rest →", TINT),
                               ("      ∃ p, input = p ++ rest", TINT)], "lean", 13, "Lean 4（定義と定理）")
T(s, 0.6, 6.05, 5.65, 0.3, "↑ 緑の定理と、その証明は Lean に残る", 13, OK, bold=True)
CODE(s, 6.55, 1.9, 6.18, 3.3, ["@annotation.tailrec", "def stripPrefix_u3f(x0: List[BigInt],",
                               "    x1: List[BigInt]): Option[List[BigInt]] =", "  ((x0, x1) match {", "    case (Nil, x2) => Some(x2)",
                               "    case ((head :: tail), Nil) => None", "    case ((c :: cs), (d :: ds)) =>",
                               "      (if (beqChar(c, d) == true)", "       then stripPrefix_u3f(cs, ds) else None)", "  })"],
     "scala", 13, "生成された Scala 3")
T(s, 6.55, 5.4, 6.18, 0.35, "Scala 側に、証明の痕跡は無い。ただの関数に見える", 15, TEXT, bold=True)
T(s, 6.55, 5.85, 6.18, 0.4, "でも「成功したら、入力は必ず p ++ rest の形」は証明済み", 15, OK, bold=True)
T(s, 6.55, 6.4, 6.18, 0.3, "Char は BigInt（コードポイント）になる。読みやすさは、そこそこ", 13, MUTED)
N(s, 45, "関数でも見てみます。"
  "左の Lean には、関数の定義と、その関数についての定理があります。"
  "右の Scala に渡るのは、関数だけです。"
  "証明の痕跡はどこにもありません。"
  "ただの末尾再帰の関数に見えます。"
  "でも、Lean の側のこの関数については、成功したら入力は必ず、何かと残りをつないだ形になる、と証明済みです。"
  "ちなみに、Char が BigInt になっているあたりは、正直あまりきれいではありません。",
  "lean/Shallot/Peg/Syntax.lean:26-29、lean/Shallot/Peg/Props.lean:13-15、scala/generated/.../Shallot.scala:1900-1906"
  "（表示のために折り返した。トークンは変えていない）。")

# ---------------------------------------------------------------- 16 証明したもの
s = new(ACT3, "証明したもの、Scala で動いているもの", SCALA)
tiles = [("PEG インタプリタ", "健全・完全・決定的"), ("型検査器", "健全かつ完全"), ("評価器", "型が付けば詰まらない"),
         ("コンパイラ", "スタック VM が同じ値を返す"), ("赤黒木", "順序と平衡を保つ"), ("JSON パーサ", "RFC 8259、往復定理")]
for i, (head, sub) in enumerate(tiles):
    x, y = 0.6 + (i % 2) * 2.95, 1.95 + (i // 2) * 1.32
    R(s, x, y, 2.8, 1.17)
    T(s, x + 0.18, y + 0.17, 2.5, 0.35, head, 17, TEXT, bold=True)
    T(s, x + 0.18, y + 0.62, 2.5, 0.35, sub, 13, OK)
CODE(s, 6.7, 1.9, 6.03, 3.95, [('$ sbt "shallotCli/run run ../examples/fact.shl"', TEXT), ("ok:3628800", OK),
                               ('$ sbt "shallotCli/run run ../examples/collatz.shl"', TEXT), ("ok:111", OK),
                               (r'$ sbt "shallotCli/run eval \"1 + 2 * 3\""', TEXT), ("ok:7", OK),
                               ("$ scripts/json-suite.sh", TEXT), ("json-suite: OK (318 files, Lean ≡ Scala,", OK),
                               ("  y_/n_ all as required)", OK)], "term", 13, "抽出した Scala を実行（2026-11-12）")
T(s, 0.6, 6.05, 12.13, 0.35, "CLI の構文解析・型検査・評価は、すべて Lean から抽出したコード", 16, TEXT, bold=True)
T(s, 0.6, 6.5, 12.13, 0.3, "リポジトリ全体：Lean 1,487ファイル・約32.7万行、sorry 0（2026-11 時点）", 13, MUTED)
N(s, 40, "lean4-peg で証明したものです。"
  "小さな言語の処理系を、構文解析から型検査、評価、コンパイラまで証明しています。"
  "右は、抽出した Scala を昨日実際に走らせた結果です。"
  "階乗もコラッツも、Lean で証明した定義から抽出したコードが、Scala として動いています。"
  "JSON のパーサは、テストスイート318本で、Lean 版と Scala 版の判定が全部一致しました。",
  "README の What is proven。右の出力は 2026-11-12 に実行して採ったもの（json-suite の出力は表示のために折り返した）。"
  "行数とファイル数は git ls-files で実測。")

# ---------------------------------------------------------------- 17 証明がバグを見つけた
s = new(ACT3, "証明が、60件のテストが踏まなかった穴を見つけた", SCALA)
CODE(s, 0.6, 1.9, 5.7, 1.5, ["def id ( x : int ) : int = x", "( 1 + 2 )"], "shallot", 15, "Shallot（証明つきの小さな言語）")
B(s, 0.6, 3.48, 5.7, 0.55, [[("→  ", {"color": DIM}), ("parse-SyntaxError", {"font": MONO, "color": BAD, "bold": True})]],
  fill=None, line=BAD, size=16, lw=1.5)
CODE(s, 0.6, 4.4, 5.7, 1.1, ["def id ( x : int ) : int = x + 0", "( 1 + 2 )"], "shallot", 15)
B(s, 0.6, 5.58, 5.7, 0.55, [[("→  ", {"color": DIM}), ("ok:3", {"font": MONO, "color": OK, "bold": True})]], fill=None, line=OK,
  size=16, lw=1.5)
T(s, 6.8, 1.92, 5.9, 0.3, "何が起きているか", 14, MUTED, bold=True)
for i, body in enumerate(["構文解析器が x ( 1 + 2 ) を関数呼び出しとして読む", "関数の本体が、境界をまたいで次の式を飲み込む",
                          "後ろに式が残らず、構文エラーになる"]):
    y = 2.35 + i * 0.68
    num(s, 6.8, y, i + 1, MUTED, 0.46)
    T(s, 7.45, y, 5.28, 0.46, body, 15, TEXT, anchor="m")
B(s, 6.8, 4.5, 5.93, 1.25, "「印字して構文解析すると元に戻る」を証明しようとして、証明が通らない場所として見つかった。"
  "定理には、この形を除く条件を明示した", fill=None, line=LEAN, size=15, align="l", pad=0.2, lw=2, ls=1.3)
T(s, 6.8, 5.95, 5.93, 0.4, "60件の差分テストは、この形を一度も踏んでいなかった", 16, AGENT, bold=True)
N(s, 40, "証明がバグを見つけた話もあります。"
  "関数の本体が変数1つで、そのあとに括弧で始まる式が来ると、構文エラーになります。"
  "本体を x たす 0 にすると通ります。"
  "構文解析器が、x と括弧を、関数呼び出しとして読んでしまうからです。"
  "60件の差分テストは、この形を一度も踏んでいませんでした。"
  "往復定理を証明しようとしたら、証明が通らない場所として、これが見つかりました。"
  "文法はまだ直していません。"
  "定理の側に、この形を除くという条件を明示しています。",
  "lean/Shallot/Syntax/Roundtrip.lean:18-27、ガード sepOkB は同 86-89、記録は docs/roadmap.md。"
  "左の2つの実行結果は 2026-11-12 に抽出した Scala の CLI で再現したもの。")

# ---------------------------------------------------------------- 18 信頼の境界
s = new(ACT3, "正直な話：証明が守るのは Lean の中まで", SCALA)
B(s, 0.6, 1.95, 4.6, 3.45, [[("証明済み", {"color": OK, "bold": True, "size": 22})], [("Lean の中", {"color": MUTED, "size": 14})], "",
                            "定義・定理・証明", "カーネルが毎回検査", "公理の検査 9,085 箇所"], fill=PANEL, line=OK, size=16, lw=2.5, ls=1.3)
B(s, 8.13, 1.95, 4.6, 3.45, [[("信頼しているだけ", {"color": MUTED, "bold": True, "size": 22})],
                             [("Lean の外", {"color": MUTED, "size": 14})], "", "Lens 抽出器（未検証）", "手書きランタイム 104行",
                             "Scala コンパイラ、JVM"], fill=None, line=MUTED, size=16, lw=2, dash=True, ls=1.3)
B(s, 5.5, 2.35, 2.33, 2.65, [[("橋：突き合わせ", {"bold": True, "size": 15, "color": AGENT})], "", "Lean の実行", "＝ 期待値", "＝ 抽出した Scala",
                             "", [("60 ケース", {"bold": True})], [("JSON 318 本", {"bold": True})]], fill=PANEL2, size=13)
A(s, 5.22, 3.675, 5.48, 3.675, MUTED, 2.0, head=False)
A(s, 7.85, 3.675, 8.11, 3.675, MUTED, 2.0, head=False)
B(s, 0.6, 5.7, 7.23, 0.95, "抽出器のレビューで、変数捕獲のバグが17件見つかった（全部直して回帰テストにした）", fill=None, line=BAD, size=15,
  lw=2, pad=0.2)
T(s, 8.13, 5.7, 4.6, 0.95, "差分テストは証明ではない。\n保証は「抽出器が正しければ」", 16, TEXT, bold=True, anchor="m", ls=1.3)
N(s, 45, "ここで3つ目の条件です。"
  "証明が守ってくれるのは、Lean の中までです。"
  "抽出器の Lens は検証していません。"
  "手書きのランタイムも、Scala コンパイラも、JVM も、信頼しているだけです。"
  "そのあいだは、Lean の実行結果と Scala の実行結果を突き合わせて埋めています。"
  "抽出器をレビューしたときには、変数捕獲のバグが17件見つかりました。"
  "全部直しましたが、差分テストは証明ではありません。"
  "保証は、抽出器が正しければ、という条件つきです。",
  "README の Trusted computing base、docs/guide/05-lens.md、docs/roadmap.md（M3：TCB レビューで捕獲バグ17件）、"
  "corpus/golden/all.jsonl（60行）、scripts/json-suite.sh。")

# ---------------------------------------------------------------- 19 利点と欠点
s = new(ACT3, "利点と欠点", SCALA)
pros = [("検査器は言いくるめられない", "エージェントが嘘をついても、ビルドが落ちる"), ("読む量が減る", "証明ではなく、定理の文と公理の一覧を読む"),
        ("テストが踏まない穴を見つける", "境界条件を1件、証明が見つけた"), ("出てくるのは読める Scala", "癖はあるが、既存のコードから呼べる")]
cons = [("文が間違っていれば、間違いを証明する", "定理の文を読める人が要る"), ("抽出器は未検証", "変数捕獲のバグ17件を直した実績つき"),
        ("生成コードに癖がある", "数はすべて BigInt、深い再帰に 256MB のスタック"), ("渡せるのは純粋な部分だけ", "partial や独自の型クラスは抽出できない"),
        ("手間はゼロではない", "未解決問題の証明では 19日、416発話")]
for x, w_, head, col, items, step in [(0.6, 5.85, "利点", OK, pros, 1.05), (6.88, 5.85, "欠点", BAD, cons, 0.86)]:
    R(s, x, 1.85, w_, 4.95)
    T(s, x + 0.3, 2.0, 3, 0.4, head, 20, col, bold=True)
    for i, (a, b) in enumerate(items):
        y = 2.6 + i * step
        R(s, x + 0.32, y + 0.1, 0.16, 0.16, col, shape=MSO_SHAPE.OVAL)
        T(s, x + 0.65, y, w_ - 0.9, 0.35, a, 17, TEXT, bold=True)
        T(s, x + 0.65, y + 0.38, w_ - 0.9, 0.3, b, 13, MUTED)
N(s, 45, "整理します。"
  "利点は4つです。"
  "検査器は言いくるめられない。"
  "人間が読む量が減る。"
  "テストが踏まない穴を見つける。"
  "そして、出てくるのは読める Scala です。"
  "欠点は5つです。"
  "文が間違っていれば、間違いを証明してしまう。"
  "だから、定理の文を読める人が要ります。"
  "抽出器は未検証。"
  "生成コードには癖があって、数は全部 BigInt、深い再帰には大きなスタックが要ります。"
  "渡せるのは純粋な部分だけ。"
  "そして、手間はゼロではありません。",
  "ここまでの各スライドの出典と同じ。256MB のスタックは scala/runtime の Stack.run と CLI の Main.scala。")

# ---------------------------------------------------------------- 20 使いどころ
s = new(ACT3, "全部は証明しない。間違えられない芯だけ証明する", SCALA)
R(s, 0.6, 1.95, 7.4, 4.65, PANEL, SCALA, 2.5, 0.2)
T(s, 0.95, 2.15, 6.7, 0.4, "普段の Scala（殻）", 20, SCALA, bold=True)
T(s, 0.95, 2.65, 6.7, 0.35, "Cats Effect / ZIO、Play / Pekko、DB、HTTP、画面", 14, MUTED)
B(s, 2.0, 3.45, 4.6, 2.6, [[("証明つきの芯", {"color": LEAN, "bold": True, "size": 22})], "", "Lean で書いて証明し、", "Scala に抽出した純粋関数"],
  fill=INK, line=LEAN, size=15, lw=2.5, radius=0.2)
T(s, 8.5, 1.98, 4.23, 0.3, "芯の候補", 14, MUTED, bold=True)
for i, c in enumerate(["料金・按分・丸めの計算", "権限の判定（発表1の続き）", "パーサ、バリデーション", "状態遷移"]):
    B(s, 8.5, 2.4 + i * 0.7, 4.23, 0.56, c, fill=PANEL2, size=16, bold=True, align="l", pad=0.25, radius=0.1)
T(s, 8.5, 5.3, 4.23, 0.3, "ここは提案。業務での実績はまだ無い", 13, DIM)
T(s, 8.5, 5.8, 4.23, 0.8, "向かないもの：I/O が主役の所、画面、速さが命の内側ループ", 14, MUTED, ls=1.3)
N(s, 35, "では、仕事でどう使うか。"
  "全部を証明する必要はありません。"
  "間違えられない芯だけを Lean で書いて証明し、Scala に落とします。"
  "外側は普段の Scala です。"
  "Cats Effect でも ZIO でも Play でも構いません。"
  "芯の候補は、料金や按分の計算、権限の判定、パーサなどです。"
  "ここは提案です。"
  "業務での実績は、まだありません。"
  "それでも、検討に値すると私は思っています。",
  "connpass の概要文（「絶対に間違えてはいけない」領域）。※このスライドは全体が私見・提案。")

# ---------------------------------------------------------------- 21 まとめ
s = new(None, "エージェントが探し、Lean が確かめ、Scala が動かす", tsize=32)
T(s, 0.6, 1.95, 7.2, 0.45, "「あと俺にできるんは応援することだけや」", 20, MUTED, bold=True)
T(s, 0.6, 2.5, 7.2, 0.4, "…ではなかった。私がやっていたのは", 17, TEXT)
for i, c in enumerate(["問いを立てる", "ズルを見張る", "捨てる決断をする", "定理の文を読む"]):
    y = 3.1 + i * 0.62
    R(s, 0.68, y + 0.16, 0.18, 0.18, TEXT, shape=MSO_SHAPE.OVAL)
    T(s, 1.1, y, 6, 0.5, c, 24, TEXT, bold=True, anchor="m")
T(s, 0.6, 5.75, 7.4, 0.45, "型で嘘を防いできた Scala の人は、この世界のいちばん近くにいる", 17, AGENT, bold=True)
T(s, 0.6, 6.45, 7, 0.4, "github.com/kmizu/lean4-peg", 18, TEXT, font=MONO)
triad(s, 10.4, 4.15, roles=["探す", "確かめる", "動かす"], center="人が問う")
N(s, 45, "最後に、冒頭の言葉に戻ります。"
  "『あと俺にできるんは応援することだけや』。"
  "数え直してみると、そうではありませんでした。"
  "問いを立てる。"
  "ズルを見張る。"
  "捨てる決断をする。"
  "定理の文を読む。"
  "これが、私に残った仕事でした。"
  "エージェントが探し、Lean が確かめ、Scala が動かす。"
  "そして、人が問う。"
  "型で嘘を防いできた Scala の人は、この世界のいちばん近くにいると思います。"
  "ありがとうございました。",
  "ここまでの各スライド。※最後の一文は私見。")

# ---------------------------------------------------------------- ページ番号と書き出し
for i, s in enumerate(SLIDES, 1):
    T(s, 11.73, 7.08, 1.0, 0.25, f"{i} / {len(SLIDES)}", 11, DIM, align="r")
out = os.path.join(HERE, "techbar22.review.pptx")
prs.save(out)
with open(os.path.join(HERE, "techbar22.review_sources.md"), "w", encoding="utf-8") as f:
    f.write("# 出典と時間配分\n\nスライドのノート欄は読み上げ用の台本だけ。数字と引用の出どころはここにまとめる。\n\n")
    for (i, sec, n, src), title in zip(SOURCES, TITLES):
        f.write(f"## {i}. {title}\n\n- 目安 {sec}秒（台本 {n}文字）\n- 出典: {src}\n\n")
chars = sum(n for _, _, n, _ in SOURCES)
print(f"{out}: {len(SLIDES)}枚、目安の合計 {sum(SECS) // 60}分{sum(SECS) % 60}秒、台本 {chars}文字（毎秒5.5文字で読むと約{chars / 5.5 / 60:.1f}分）")
for i, sec, n, _ in SOURCES:
    print(f"  {i:2d}: 目安{sec:3d}秒  台本{n:4d}字  読み上げ約{n / 5.5:3.0f}秒")
