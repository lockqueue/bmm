#!/usr/bin/env python3
"""Self-contained generator and verifier for the CostM payload table.

Scans BMMGrid.lean and BMMGrid/*.lean (excluding CostMonadAndLinter.lean, which
defines the primitive CostM combinators) for all definition-level call sites of
the 12 CostM combinators that accept a pure value payload:
  - Tier-B size-charge combinators:
      scanMatrixTracked, scanMatrixPairTracked, scanFinsetTracked
  - Unit-cost return combinator:
      retTracked
  - Per-element / sum / block-extract combinators:
      filterFinsetByTracked, filterListByTracked, findSomeListByTracked,
      tabulateFinsetTracked, sumFinsetTracked, evalSupportScanTracked,
      evalMinNbrScanTracked, scanBlockExtractTracked

Computes call-graph reachability from the headline roots and either emits the
LaTeX longtable for FORMALIZATION.tex (--latex), updates FORMALIZATION.tex
in-place (--update), or verifies 1-to-1 parity between the Lean source files and
FORMALIZATION.tex (--check).
"""

import argparse
import collections
import pathlib
import re
import sys

COMBINATORS = [
    "retTracked",
    "scanMatrixTracked",
    "scanMatrixPairTracked",
    "scanFinsetTracked",
    "filterFinsetByTracked",
    "filterListByTracked",
    "findSomeListByTracked",
    "tabulateFinsetTracked",
    "sumFinsetTracked",
    "evalSupportScanTracked",
    "evalMinNbrScanTracked",
    "scanBlockExtractTracked",
]

SCAN_COMBINATORS = {
    "scanMatrixTracked",
    "scanMatrixPairTracked",
    "scanFinsetTracked",
}

OTHER_COMBINATORS = [
    "filterFinsetByTracked",
    "filterListByTracked",
    "findSomeListByTracked",
    "tabulateFinsetTracked",
    "sumFinsetTracked",
    "evalSupportScanTracked",
    "evalMinNbrScanTracked",
    "scanBlockExtractTracked",
]

HEADLINE_ROOTS = [
    "computableBMMTracked",
    "computableTriangleDetectionTracked",
    "cappedABDecompositionTracked",
    "cappedADecompositionConcreteTracked",
    "twoStage_compose",
]

MODULE_ORDER = [
    "ObliviousSampler.lean",
    "ApproxGridNorm.lean",
    "MinDegreeAndDyadicSift.lean",
    "Decomp2D.lean",
    "DyadicBucketingAndGoodCube.lean",
    "Decomp3DPotential.lean",
    "Decomp3D.lean",
    "TriangleAndBMM.lean",
]

EXPECTED_COUNTS = {
    "total": 107,
    "retTracked": 45,
    "scan_total": 51,
    "scanFinsetTracked": 4,
    "scanMatrixTracked": 32,
    "scanMatrixPairTracked": 15,
    "other_total": 11,
    "filterFinsetByTracked": 1,
    "filterListByTracked": 3,
    "findSomeListByTracked": 1,
    "tabulateFinsetTracked": 1,
    "sumFinsetTracked": 1,
    "evalSupportScanTracked": 2,
    "evalMinNbrScanTracked": 1,
    "scanBlockExtractTracked": 1,
    "on_path": 106,
    "off_path": 1,
    "non_def_scans": 12,
}

COMB_RE = re.compile(r"\b(" + "|".join(COMBINATORS) + r")\b")
SCAN_RE = re.compile(r"\b(" + "|".join(sorted(SCAN_COMBINATORS)) + r")\b")
DEF_RE = re.compile(
    r"^(?:/--.*-\/\s*)?(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|unsafe\s+|partial\s+)*(?:noncomputable\s+)?"
    r"def\s+([A-Za-z0-9_'\.]+)"
)
THM_RE = re.compile(
    r"^(?:/--.*-\/\s*)?(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+)*(?:noncomputable\s+)?"
    r"(?:theorem|lemma)\s+([A-Za-z0-9_'\.]+)"
)
STOP_RE = re.compile(
    r"^(?:/--.*-\/\s*)?(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|unsafe\s+|partial\s+)*(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|example|"
    r"section|end|namespace|#verify)\b|^/-!"
)
IDENT_RE = re.compile(r"\b([A-Za-z0-9_'\.]+)\b")


def latex_escape_code(text: str, allow_camel_break: bool = False) -> str:
  r"""Formats a compact code snippet for \code{...} in LaTeX."""
  s = " ".join(text.strip().split())
  if len(s) > 64:
    s = s[:61] + "..."
  if allow_camel_break:
    s = re.sub(r"([a-z]{4,})([A-Z])", r"\1\\allowbreak \2", s)
  replacements = [
      ("\\allowbreak ", "\x00ALLOWBREAK\x00"),
      ("\\", "\\textbackslash "),
      ("{", "\\{"),
      ("}", "\\}"),
      ("_", "\\_"),
      ("^", "\\^{}"),
      ("&", "\\&"),
      ("%", "\\%"),
      ("#", "\\#"),
      ("$", "\\$"),
      ("~", "\\textasciitilde "),
      ("≤", "<="),
      ("≥", ">="),
      ("≠", "!="),
      ("∧", "and"),
      ("∨", "or"),
      ("¬", "not "),
      ("∈", "in"),
      ("∉", "notin"),
      ("⊆", "subset"),
      ("×ˢ", "x"),
      ("×", "x"),
      ("⊕", "+"),
      ("↦", "->"),
      ("→", "->"),
      ("←", "<-"),
      ("⟨", "<"),
      ("⟩", ">"),
      ("∅", "empty"),
      ("ℝ", "R"),
      ("ℕ", "N"),
      ("ℤ", "Z"),
      ("ℚ", "Q"),
      ("α", "alpha"),
      ("β", "beta"),
      ("γ", "gamma"),
      ("δ", "delta"),
      ("ε", "eps"),
      ("μ", "mu"),
      ("ρ", "rho"),
      ("τ", "tau"),
      ("₀", "0"),
      ("₁", "1"),
      ("₂", "2"),
      ("₃", "3"),
      ("⁻¹", "\\^{}(-1)"),
      ("⁻", "-"),
      ("¹", "1"),
      ("ℓ", "l"),
      ("\x00ALLOWBREAK\x00", "\\allowbreak "),
  ]
  for old, new in replacements:
    s = s.replace(old, new)
  return s


def charging_rationale(comb: str, expr: str, on_path: bool) -> str:
  """Returns the exact _snd formula and callback status for a call site."""
  path_note = ""
  if not on_path:
    path_note = "Off-headline helper/variant; "

  if comb == "scanMatrixTracked":
    return (
        path_note
        + "Charges $|U||V|+1$ (\\code{scanMatrixTracked\\_snd})."
    )
  if comb == "scanMatrixPairTracked":
    return (
        path_note
        + "Charges $|X||Y|+|Y||Z|+1$ (\\code{scanMatrixPairTracked\\_snd})."
    )
  if comb == "scanFinsetTracked":
    return (
        path_note
        + "Charges $|U|+1$ (\\code{scanFinsetTracked\\_snd})."
    )
  if comb == "filterFinsetByTracked":
    return (
        path_note
        + "Charges $|S|+1$ (\\code{filterFinsetByTracked\\_snd}); predicate is "
        "an untracked \\code{Bool} function ($O(1)$-word work under Class~B)."
    )
  if comb == "filterListByTracked":
    return (
        path_note
        + "Charges $|xs|+1$ (\\code{filterListByTracked\\_snd}); predicate "
        "untracked."
    )
  if comb == "findSomeListByTracked":
    return (
        path_note
        + "Charges $\\le |xs|+1$ (\\code{findSomeListByTracked\\_snd\\_le}; "
        "$\\le m^3+1$ bound used); callback untracked; $m^3$-list "
        "\\code{blockSubTriplesList m} uncharged."
    )
  if comb == "tabulateFinsetTracked":
    return (
        path_note
        + "Charges $\\sum_{x\\in S} (f\\ x).2 + 1$ "
        "(\\code{tabulateFinsetTracked\\_snd}; no domain-size term; each "
        "callback charges $\\ge 1$)."
    )
  if comb == "sumFinsetTracked":
    return (
        path_note
        + "Charges $\\sum_{x\\in S} (f\\ x).2 + 1$ "
        "(\\code{sumFinsetTracked\\_snd}; no domain-size term; each callback "
        "charges $\\ge 1$)."
    )
  if comb == "evalSupportScanTracked":
    return (
        path_note
        + "Charges $|U||V|+1$ (\\code{evalSupportScanTracked\\_snd}); "
        "predicate untracked."
    )
  if comb == "evalMinNbrScanTracked":
    return (
        path_note
        + "Charges $\\sum_{xz\\in S}(1 + \\min(|N_1\\ xz|,|N_2\\ xz|)) + 1$ "
        "(\\code{evalMinNbrScanTracked\\_snd})."
    )
  if comb == "scanBlockExtractTracked":
    return (
        path_note
        + "Charges $3m^2+1$ (\\code{scanBlockExtractTracked\\_snd})."
    )
  # retTracked
  if any(
      k in expr
      for k in (
          "restrictSubrect",
          "zeroOutSubrect",
          "submatZeroExt",
          "rowSupport",
          "outerDyadicBucket",
          "innerDyadicBucket",
      )
  ):
    return (
        path_note
        + "Unit return ($+1$, \\code{retTracked\\_snd}); submatrix/bucket scan "
        "is charged by the paired \\code{scan*Tracked} call in the same step."
    )
  if any(k in expr for k in ("indexFinset", "getD")):
    return (
        path_note
        + "Unit return ($+1$, \\code{retTracked\\_snd}); $O(1)$ array index "
        "under Class~B."
    )
  if "List.range" in expr or "List.ofFn" in expr:
    return (
        path_note
        + "Unit return ($+1$, \\code{retTracked\\_snd}) of small index list "
        "($O(D)$ scales or tuple coordinates); downstream loop charges "
        "per-element work."
    )
  if "acc + entry.2" in expr or "acc + v" in expr:
    return (
        path_note
        + "Unit step charge ($+1$, \\code{retTracked\\_snd}) for "
        "table-contraction accumulator addition "
        "($O(d \\log B + \\log |X|)$-bit counter; see Class~B)."
    )
  if "constructSmallTwoStageSampler" in expr:
    return (
        path_note
        + "Unit return ($+1$, \\code{retTracked\\_snd}) for"
        " \\code{construct\\allowbreak Small\\allowbreak TwoStage\\allowbreak"
        " Sampler} (uncharged \\code{[Y.toList]} in off-path helper)."
    )
  if "clearMatEntry" in expr:
    return (
        path_note
        + "Unit return ($+1$, \\code{retTracked\\_snd}) for single-cell "
        "update \\code{clearMatEntry} ($O(1)$ 2D-array write under Class~B)."
    )
  return (
      path_note
      + "Unit return ($+1$, \\code{retTracked\\_snd}) packaging already-bound "
      "values/accumulators."
  )


def analyze_lean_dir(lean_dir: pathlib.Path):
  """Parses BMMGrid.lean and BMMGrid/*.lean and returns (sites, non_def_scans, reachable, unattributed)."""
  bmm_dir = lean_dir / "BMMGrid"
  files = [bmm_dir / m for m in MODULE_ORDER]
  for extra in sorted(bmm_dir.glob("*.lean")):
    if extra.name != "CostMonadAndLinter.lean" and extra not in files:
      files.append(extra)
  root_file = lean_dir / "BMMGrid.lean"
  if root_file.exists():
    files.append(root_file)

  defs = {}
  def_code_lines = collections.defaultdict(list)
  for f in files:
    bname = f.name
    lines = f.read_text(encoding="utf-8").splitlines()
    cur_def = None
    in_comment = False
    for idx, line in enumerate(lines, 1):
      s = line.strip()
      if s.startswith("/-"):
        if "-/" not in s[2:]:
          in_comment = True
          continue
        s_after = s.split("-/", 1)[1].strip()
        if not s_after:
          continue
        s = s_after
      if in_comment:
        if "-/" in s:
          in_comment = False
        continue
      if s.startswith("--"):
        continue
      if STOP_RE.match(s):
        m_def = DEF_RE.match(s)
        if m_def:
          cur_def = m_def.group(1)
          defs[cur_def] = bname
        else:
          cur_def = None
      if cur_def:
        code_part = line.split("--")[0]
        def_code_lines[cur_def].append((bname, idx, code_part))

  edges = collections.defaultdict(set)
  for d, dlines in def_code_lines.items():
    for _, _, code_part in dlines:
      for m in IDENT_RE.finditer(code_part):
        tok = m.group(1)
        if tok in defs and tok != d:
          edges[d].add(tok)

  reachable = set()
  queue = collections.deque(r for r in HEADLINE_ROOTS if r in defs)
  while queue:
    u = queue.popleft()
    if u in reachable:
      continue
    reachable.add(u)
    for v in edges[u]:
      if v not in reachable:
        queue.append(v)

  sites = []
  non_def_scans = []
  unattributed = []
  for f in files:
    bname = f.name
    lines = f.read_text(encoding="utf-8").splitlines()
    cur_def = None
    in_thm_stmt = False
    in_comment = False
    for idx, line in enumerate(lines, 1):
      s = line.strip()
      if s.startswith("/-"):
        if "-/" not in s[2:]:
          in_comment = True
          for m in SCAN_RE.finditer(line):
            non_def_scans.append((bname, idx, m.group(1), "docstring"))
          continue
        doc_part, s_after = s.split("-/", 1)
        for m in SCAN_RE.finditer(doc_part):
          non_def_scans.append((bname, idx, m.group(1), "docstring"))
        s = s_after.strip()
        if not s:
          continue
      if in_comment:
        for m in SCAN_RE.finditer(line):
          non_def_scans.append((bname, idx, m.group(1), "docstring"))
        if "-/" in s:
          in_comment = False
        continue
      if s.startswith("--"):
        for m in SCAN_RE.finditer(line):
          non_def_scans.append((bname, idx, m.group(1), "comment"))
        continue
      if STOP_RE.match(s):
        m_def = DEF_RE.match(s)
        m_thm = THM_RE.match(s)
        cur_def = m_def.group(1) if m_def else None
        in_thm_stmt = bool(m_thm)
      code_part = line.split("--")[0]
      if cur_def and cur_def not in COMBINATORS:
        for m in COMB_RE.finditer(code_part):
          comb = m.group(1)
          after = code_part[m.end() :].strip()
          if len(after) < 28:
            cont = [after] if after else []
            for lookahead in range(idx, min(idx + 3, len(lines))):
              nxt = lines[lookahead].split("--")[0].strip()
              if not nxt or STOP_RE.match(nxt):
                break
              cont.append(nxt)
              if len(" ".join(cont)) >= 48:
                break
            after = " ".join(cont).strip()
          on_path = cur_def in reachable
          sites.append({
              "file": bname,
              "line": idx,
              "def": cur_def,
              "comb": comb,
              "expr": after if after else code_part.strip(),
              "on_path": on_path,
          })
      else:
        for m in SCAN_RE.finditer(code_part):
          kind = "statement" if in_thm_stmt else "proof"
          non_def_scans.append((bname, idx, m.group(1), kind))
        for m in COMB_RE.finditer(code_part):
          if m.group(1) not in SCAN_COMBINATORS and not in_thm_stmt:
            pass
      if (
          in_thm_stmt
          and ":=" in code_part
          and not code_part.lstrip().startswith("let ")
      ):
        in_thm_stmt = False

  # Verify every combinator token inside any def body was attributed to a site
  site_keys = {(s["file"], s["line"], s["comb"]) for s in sites}
  for d, dlines in def_code_lines.items():
    if d in COMBINATORS:
      continue
    for bname, idx, code_part in dlines:
      for m in COMB_RE.finditer(code_part):
        if (bname, idx, m.group(1)) not in site_keys:
          unattributed.append((bname, idx, d, m.group(1)))

  return sites, non_def_scans, reachable, unattributed


def generate_latex(sites, non_def_scans) -> str:
  """Generates the LaTeX block between % BEGIN_PAYLOAD_SITES and % END_PAYLOAD_SITES."""
  total_scans = sum(1 for s in sites if s["comb"] in SCAN_COMBINATORS) + len(
      non_def_scans
  )
  out = []
  out.append("% BEGIN_PAYLOAD_SITES")
  out.append("{\\scriptsize")
  out.append("\\setlength{\\tabcolsep}{2.5pt}")
  out.append(
      "\\begin{longtable}{@{}r >{\\raggedright\\arraybackslash}p{1.91in} "
      ">{\\raggedright\\arraybackslash}p{1.20in} c "
      ">{\\raggedright\\arraybackslash}p{1.34in} "
      ">{\\raggedright\\arraybackslash}p{1.39in}@{}}"
  )
  out.append("\\toprule")
  out.append(
      "\\textbf{\\#} & \\textbf{Module:Line \\& Enclosing \\code{def}} & "
      "\\textbf{Combinator} & \\textbf{On Path} & "
      "\\textbf{Payload Snippet} & \\textbf{Charging Rationale} \\\\"
  )
  out.append("\\midrule")
  out.append("\\endhead")
  out.append("\\bottomrule")
  out.append("\\endfoot")
  for idx, s in enumerate(sites, 1):
    loc = f"\\code{{{latex_escape_code(s['file'])}:{s['line']}}}"
    fn = f"\\code{{{latex_escape_code(s['def'])}}}"
    comb = f"\\code{{{latex_escape_code(s['comb'])}}}"
    on_p = "yes" if s["on_path"] else "no"
    expr = f"\\code{{{latex_escape_code(s['expr'], allow_camel_break=True)}}}"
    rat = charging_rationale(s["comb"], s["expr"], s["on_path"])
    out.append(
        f"{idx} & {loc}\\newline {fn} & {comb} & {on_p} & {expr} & {rat} \\\\"
    )
  out.append("\\end{longtable}")
  out.append("}")
  out.append("")
  out.append(
      f"\\emph{{Additional {len(non_def_scans)} statement/proof/docstring "
      f"occurrences of \\code{{scan*Tracked}} (making {total_scans} total "
      r"\code{scan*Tracked} grep matches outside "
      r"\code{CostMonadAndLinter.lean})}: "
      + ", ".join(
          f"\\code{{{latex_escape_code(b)}:{l}}} ({kind})"
          for b, l, _, kind in non_def_scans
      )
      + "."
  )
  out.append("% END_PAYLOAD_SITES")
  return "\n".join(out)


def check_parity(lean_dir: pathlib.Path, tex_path: pathlib.Path) -> int:
  """Verifies payload table parity, per-combinator splits, and prose counts."""
  sites, non_def_scans, _, unattributed = analyze_lean_dir(lean_dir)
  if unattributed:
    print(
        f"ERROR: unattributed combinator tokens in def bodies: {unattributed}",
        file=sys.stderr,
    )
    return 1

  counts = collections.Counter(s["comb"] for s in sites)
  actual = {
      "total": len(sites),
      "retTracked": counts["retTracked"],
      "scan_total": sum(counts[c] for c in SCAN_COMBINATORS),
      "scanFinsetTracked": counts["scanFinsetTracked"],
      "scanMatrixTracked": counts["scanMatrixTracked"],
      "scanMatrixPairTracked": counts["scanMatrixPairTracked"],
      "other_total": sum(counts[c] for c in OTHER_COMBINATORS),
      "filterFinsetByTracked": counts["filterFinsetByTracked"],
      "filterListByTracked": counts["filterListByTracked"],
      "findSomeListByTracked": counts["findSomeListByTracked"],
      "tabulateFinsetTracked": counts["tabulateFinsetTracked"],
      "sumFinsetTracked": counts["sumFinsetTracked"],
      "evalSupportScanTracked": counts["evalSupportScanTracked"],
      "evalMinNbrScanTracked": counts["evalMinNbrScanTracked"],
      "scanBlockExtractTracked": counts["scanBlockExtractTracked"],
      "on_path": sum(1 for s in sites if s["on_path"]),
      "off_path": sum(1 for s in sites if not s["on_path"]),
      "non_def_scans": len(non_def_scans),
  }

  for k, exp in EXPECTED_COUNTS.items():
    if actual[k] != exp:
      print(
          f"ERROR: count mismatch for {k}: "
          f"actual={actual[k]} vs expected={exp}",
          file=sys.stderr,
      )
      return 1

  tex_text = tex_path.read_text(encoding="utf-8")
  if (
      tex_text.count("% BEGIN_PAYLOAD_SITES") != 1
      or tex_text.count("% END_PAYLOAD_SITES") != 1
  ):
    print(
        "ERROR: FORMALIZATION.tex must contain unique "
        "% BEGIN_PAYLOAD_SITES / % END_PAYLOAD_SITES markers.",
        file=sys.stderr,
    )
    return 1
  expected_block = generate_latex(sites, non_def_scans)
  if expected_block not in tex_text:
    print(
        "ERROR: payload table in FORMALIZATION.tex is out of sync "
        "with BMMGrid/*.lean (re-run scripts/gen_payload_table.py --update).",
        file=sys.stderr,
    )
    return 1

  for f in sorted((lean_dir / "BMMGrid").glob("*.lean")):
    if f.name == "CostMonadAndLinter.lean":
      continue
    for lno, ltxt in enumerate(f.read_text(encoding="utf-8").splitlines(), 1):
      code_part = ltxt.split("--")[0]
      if "Prod.mk" in code_part:
        print(
            f"ERROR: raw Prod.mk found in {f.name}:{lno}: {code_part.strip()}",
            file=sys.stderr,
        )
        return 1

  required_prose_snippets = [
      f"{actual['scan_total']} definition-level sites",
      f"({actual['scanFinsetTracked']} sites)",
      f"({actual['scanMatrixTracked']} sites)",
      f"({actual['scanMatrixPairTracked']} sites)",
      f"{actual['retTracked']} definition-level sites",
      f"{actual['other_total']} definition-level sites",
      f"\\textbf{{{actual['total']}}} definition-level call sites, "
      f"\\textbf{{{actual['on_path']}}} lie on the call graph",
  ]
  for snip in required_prose_snippets:
    if snip not in tex_text:
      print(
          "ERROR: FORMALIZATION.tex prose missing expected count snippet: "
          f"{snip!r}",
          file=sys.stderr,
      )
      return 1

  print(
      f"Verified {actual['total']}-site CostM payload table parity: "
      f"{actual['total']} sites ({actual['retTracked']} retTracked, "
      f"{actual['scan_total']} scan*Tracked [{actual['scanFinsetTracked']}/"
      f"{actual['scanMatrixTracked']}/{actual['scanMatrixPairTracked']}], "
      f"{actual['other_total']} per-element/sum/block-extract; "
      f"{actual['on_path']} on-headline-path, {actual['off_path']} off-path; "
      f"+{actual['non_def_scans']} statement/proof/docstring scan*Tracked = "
      f"{actual['scan_total'] + actual['non_def_scans']})."
  )
  return 0


def main() -> int:
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument(
      "--lean-dir",
      type=pathlib.Path,
      default=pathlib.Path(__file__).resolve().parent.parent,
      help="Path to the lean/ directory.",
  )
  parser.add_argument(
      "--latex",
      action="store_true",
      help="Print the LaTeX payload table block to stdout.",
  )
  parser.add_argument(
      "--update",
      action="store_true",
      help="Update the payload table block in FORMALIZATION.tex in-place.",
  )
  parser.add_argument(
      "--check",
      action="store_true",
      help="Verify parity between BMMGrid/*.lean and FORMALIZATION.tex.",
  )
  args = parser.parse_args()

  sites, non_def_scans, _, _ = analyze_lean_dir(args.lean_dir)
  tex_path = args.lean_dir / "FORMALIZATION.tex"

  if args.latex:
    print(generate_latex(sites, non_def_scans))
    return 0
  if args.update:
    text = tex_path.read_text(encoding="utf-8")
    new_block = generate_latex(sites, non_def_scans)
    pattern = re.compile(
        r"% BEGIN_PAYLOAD_SITES.*?% END_PAYLOAD_SITES", re.DOTALL
    )
    if not pattern.search(text):
      print("ERROR: markers not found in FORMALIZATION.tex", file=sys.stderr)
      return 1
    tex_path.write_text(
        pattern.sub(lambda _: new_block, text), encoding="utf-8"
    )
    print(f"Updated {len(sites)}-site table in {tex_path}")
    return 0
  if args.check:
    return check_parity(args.lean_dir, tex_path)

  parser.print_help()
  return 0


if __name__ == "__main__":
  sys.exit(main())
