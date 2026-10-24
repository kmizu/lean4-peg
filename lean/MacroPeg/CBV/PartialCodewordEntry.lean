import MacroPeg.CBV.PartialCodewordTotality
import MacroPeg.CBV.LeadingReplayStar

/-! Both physical capture branches and the full partial entry transfer.
The continuation premise is intended for a recursive table induction. -/
namespace Shallot.MacroPeg.CBV.PartialCodewordEntry
open PartialCodewordCapture (runA argument restArgument look captured longTest)
open PartialCodewordPreflight (checkBody)
open PartialCodewordExecution (firstPiece secondPiece pieces_join)
open RuntimeShiftFilter (block scanner)
open CodewordReplay (power)
open ClockFreezing (Table)
open LastCodewordCandidate (literal_at)

def branches (binary unary : Nat) : MExp :=
  .alt (.seq longTest (.call binary [runA,restArgument]))
    (.seq (.notP longTest) (.call unary [runA]))
def entry (binary unary : Nat) : MExp :=
  .seq (look (.call 0 [runA])) (branches binary unary)

private theorem look_ok (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (a : MExp) (p q : Nat)
    (h : evV g x s T E a p=some (some q)) :
    evV g x s T E (look a) p=some (some p) := by
  change evV g x s T E (.andP a) p=_
  rw [CallLookahead.evV_peek,h]
  rfl

private theorem source_body_at (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (k n p : Nat) (rest : List Char) (b : MExp) (hp : p≤x.length)
    (hs : sfx x p=power (block k) (n+1)++firstPiece k++rest) :
    evV g x s T [captured k n] (.seq scanner (.seq (.param 0) b)) p=
      evV g x s T [captured k n] b rest.length := by
  have hs' : sfx x p=block k++(captured k n++rest) := by
    simpa [captured,power,firstPiece,List.replicate_succ,List.append_assoc] using hs
  have hhead := PrefixCodeCapture.scanner_at g x s T [captured k n] p k _ hp hs'
  have hsr : sfx x (captured k n++rest).length=captured k n++rest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨block k,hs'⟩).choose_spec
  have hreplay : evV g x s T [captured k n] (.param 0) (captured k n++rest).length=some (some rest.length) :=
    literal_at g x s T [] (captured k n) rest _ hsr
  rw [evV_seq_ok hhead,evV_seq_ok hreplay]

private theorem split_body_at (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (k n p : Nat) (rest : List Char) (b : MExp) (hb : b.FirstOrder) (hp : p≤x.length)
    (hs : sfx x p=power (block k) (n+2)++firstPiece k++rest) :
    evV g x s T [firstPiece k,secondPiece k n]
      (.seq (.lit ['#']) (.seq (.param 0) (CodewordControlFilter.wholeView b)))
      ('#'::(firstPiece k++rest)).length=
      evV g x s T [captured k (n+1)] b rest.length := by
  rw [←PartialCodewordPreflight.bodies_eq g x s T k n p rest b hb hp hs]
  exact source_body_at g x s T k (n+1) p rest b hp hs

/-- The long branch evaluates both real arguments in the original E,
then passes the reconstructed whole value to any first-order continuation. -/
theorem positive_branch (g : MGrammar) (x : List Char) (m binary unary k n p : Nat)
    (E : List (List Char)) (rest : List Char) (b : MExp) (hb : b.FirstOrder)
    (hp : p≤x.length)
    (rule : ruleAtM g.rules binary=some ⟨2,.seq (.lit ['#'])
      (.seq (.param 0) (CodewordControlFilter.wholeView b))⟩)
    (hs : sfx x p=power (block k) (n+2)++firstPiece k++rest)
    (hend : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      scanner (firstPiece k++rest).length=some none) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E (branches binary unary) p=
      evV g x .callByValueSeq (tblV g x .callByValueSeq m) [captured k (n+1)] b rest.length := by
  let T := tblV g x .callByValueSeq (m+1)
  let r := power (block k) (n+1)++firstPiece k++rest
  have hs' : sfx x p=block k++r := by simpa [r,power,List.replicate_succ,List.append_assoc] using hs
  have hfirst := PrefixCodeCapture.scanner_at g x .callByValueSeq T E p k r hp hs'
  have hr : r.length≤x.length := by
    have hh := congrArg List.length hs'
    rw [length_sfx x hp,List.length_append] at hh
    omega
  have hsr : sfx x r.length=r := sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨block k,hs'⟩).choose_spec
  have hs'' : sfx x r.length=block k++(power (block k) n++firstPiece k++rest) := by
    simpa [r,power,List.replicate_succ,List.append_assoc] using hsr
  have hsecond := PrefixCodeCapture.scanner_at g x .callByValueSeq T E r.length k _ hr hs''
  have hlong : evV g x .callByValueSeq T E longTest p=some (some p) := by
    apply look_ok g x .callByValueSeq T E (.seq scanner scanner) p _
    rw [evV_seq_ok hfirst]
    exact hsecond
  have hargs := PartialCodewordPreflight.split_arguments g x .callByValueSeq T E k n p rest hp hs hend
  have hbound : ('#'::(firstPiece k++rest)).length≤x.length := by
    have hh := congrArg List.length (show sfx x p=captured k (n+1)++('#'::(firstPiece k++rest)) by
      rw [hs,PartialCodewordPreflight.word_boundary k (n+1) rest])
    rw [length_sfx x hp,List.length_append] at hh
    omega
  have hcall : evV g x .callByValueSeq T E (.call binary [runA,restArgument]) p=
      evV g x .callByValueSeq (tblV g x .callByValueSeq m) [captured k (n+1)] b rest.length := by
    rw [evV_call_seq rule rfl,hargs]
    dsimp only [T]
    rw [valAt_tblV_succ rule _ hbound]
    exact split_body_at g x .callByValueSeq _ k n p rest b hb hp hs
  change (match evV g x .callByValueSeq T E (.seq longTest (.call binary [runA,restArgument])) p with
    | some none => evV g x .callByValueSeq T E (.seq (.notP longTest) (.call unary [runA])) p
    | other => other)=_
  rw [evV_seq_ok hlong]
  have hno : evV g x .callByValueSeq T E (.seq (.notP longTest) (.call unary [runA])) p=some none :=
    evV_seq_fail (evV_not_ok hlong)
  rw [hno]
  rw [←hcall]
  cases evV g x .callByValueSeq T E (.call binary [runA,restArgument]) p with
  | none => rfl
  | some r => cases r <;> rfl

/-- The zero-complete-word branch retains the actual first a-run, including
an empty capture. The guarded long branch cannot fall back after success. -/
theorem zero_branch (g : MGrammar) (x : List Char) (m binary unary k p : Nat)
    (E : List (List Char)) (rest : List Char) (b : MExp) (hp : p≤x.length)
    (rule : ruleAtM g.rules unary=some ⟨1,.seq (.lit ['#']) (.seq (.param 0) b)⟩)
    (hs : sfx x p=block k++(firstPiece k++rest))
    (hend : evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E
      scanner (firstPiece k++rest).length=some none) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E (branches binary unary) p=
      evV g x .callByValueSeq (tblV g x .callByValueSeq m) [firstPiece k] b rest.length := by
  let T := tblV g x .callByValueSeq (m+1)
  let r := firstPiece k++rest
  have hscan := PrefixCodeCapture.scanner_at g x .callByValueSeq T E p k r hp hs
  have hlong : evV g x .callByValueSeq T E longTest p=some none := by
    change evV g x .callByValueSeq T E (.andP (.seq scanner scanner)) p=_
    rw [CallLookahead.evV_peek,evV_seq_ok hscan,hend]
    rfl
  have hs' : sfx x p=firstPiece k++('#'::r) := by simpa [r,block,firstPiece,List.append_assoc] using hs
  have hrun := PartialCodewordCapture.run_at g x .callByValueSeq T E k p '#' r (by decide) hp hs'
  have hcap : pre x p ('#'::r).length=firstPiece k := by
    have hh := pre_eq (sfx_is_suffix x p) hs'
    simpa only [length_sfx x hp] using hh
  have hj : ('#'::r).length≤x.length := by
    have hh := congrArg List.length hs'
    rw [length_sfx x hp,List.length_append] at hh
    omega
  have hsr : sfx x ('#'::r).length='#'::r :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨firstPiece k,hs'⟩).choose_spec
  have htail : sfx x r.length=r :=
    sfx_suffix (suffix_trans (sfx_is_suffix x ('#'::r).length) ⟨['#'],hsr⟩).choose_spec
  have hhash := literal_at g x .callByValueSeq (tblV g x .callByValueSeq m) [firstPiece k] ['#'] r _ hsr
  have hparam : evV g x .callByValueSeq (tblV g x .callByValueSeq m) [firstPiece k] (.param 0)
      r.length=some (some rest.length) := literal_at g x .callByValueSeq (tblV g x .callByValueSeq m) [] (firstPiece k) rest _ htail
  change evV g x .callByValueSeq T E (branches binary unary) p=_
  rw [branches,evV_alt_fail (evV_seq_fail hlong),evV_seq_ok (evV_not_fail hlong),
    evV_call_seq rule rfl]
  simp only [evSeqArgs,hrun,hcap]
  dsimp only [T]
  rw [valAt_tblV_succ rule _ hj,evV_seq_ok hhash,evV_seq_ok hparam]

/-- Full partial-result transfer for one actual generated call. The
continuation relation is the induction premise at the preceding ordinary
clock; all entry tests, captures, branches and failures are proved here. -/
theorem transfer (g g' : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m m' i binary unary p : Nat) (E E' : List (List Char)) (b b' : MExp)
    (hb' : b'.FirstOrder) (hp : p≤x.length)
    (sourceRule : ruleAtM g.rules i=some ⟨1,.seq scanner (.seq (.param 0) b)⟩)
    (checkRule : ruleAtM g'.rules 0=some ⟨1,checkBody⟩)
    (binaryRule : ruleAtM g'.rules binary=some ⟨2,.seq (.lit ['#'])
      (.seq (.param 0) (CodewordControlFilter.wholeView b'))⟩)
    (unaryRule : ruleAtM g'.rules unary=some ⟨1,.seq (.lit ['#']) (.seq (.param 0) b')⟩)
    (hcont : ∀ w q, q≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar m) [w] b q=
        evV g' x .callByValueSeq (tblV g' x .callByValueSeq m') [w] b' q) :
    evV g x .callByValuePar (tblV g x .callByValuePar (m+1)) E (.call i [argument]) p=
      evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E' (entry binary unary) p := by
  obtain ⟨j,ha⟩ := PartialCodewordTotality.argument_total g x .callByValuePar
    (tblV g x .callByValuePar m) (tblV_ok g x .callByValuePar m) E p hp
  have ha' : evV g x .callByValuePar (tblV g x .callByValuePar (m+1)) E argument p=some (some j) :=
    (PartialCodewordTotality.argument_context g g x .callByValuePar .callByValuePar _ _ E E p).trans ha
  have hsource : evV g x .callByValuePar (tblV g x .callByValuePar (m+1)) E (.call i [argument]) p=
      evV g x .callByValuePar (tblV g x .callByValuePar m) [pre x p j]
        (.seq scanner (.seq (.param 0) b)) p := by
    rw [evV_call_par sourceRule rfl (by decide)]
    simp only [evParArgs,ha']
    rw [valAt_tblV_succ sourceRule _ hp]
  rw [hsource]
  obtain ⟨r,hr⟩ := PartialCodewordTotality.prefix_total g x .callByValuePar
    (tblV g x .callByValuePar m) (tblV_ok g x .callByValuePar m) (pre x p j) p hp
  cases r with
  | none =>
    have hfail := (PartialCodewordTotality.preflight_failure_iff g g' hg x m m' p j E E' hp checkRule ha).mpr hr
    have hlook : evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E'
        (look (.call 0 [runA])) p=some none := by
      change evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E' (.andP (.call 0 [runA])) p=_
      rw [CallLookahead.evV_peek,hfail]
      rfl
    rw [←LeadingReplayStar.sequence_assoc g x .callByValuePar _ _ scanner (.param 0) b p,
      evV_seq_fail hr,entry,evV_seq_fail hlook]
  | some q =>
    have hq := evV_ok (tblV_ok g x .callByValuePar m) _ p hp q hr
    have hpre := PartialCodewordPreflight.source_to_preflight g g' hg x m m' p j q E E' hp checkRule ha hr
    have hlook := look_ok g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E' _ p q hpre
    rw [entry,evV_seq_ok hlook,
      ←LeadingReplayStar.sequence_assoc g x .callByValuePar _ _ scanner (.param 0) b p,
      evV_seq_ok hr,hcont _ q hq]
    obtain ⟨k,n,hcap,hs,hend⟩ := PartialCodewordPreflight.source_prefix_shape g hg x m p j q E hp ha hr
    have htail : (firstPiece k++sfx x q).length≤x.length := by
      have hl := congrArg List.length hs
      rw [length_sfx x hp,List.length_append,List.length_append] at hl
      simp only [List.length_append]
      omega
    have hend' : evV g' x .callByValueSeq (tblV g' x .callByValueSeq (m'+1)) E'
        scanner (firstPiece k++sfx x q).length=some none :=
      (PartialCodewordPreflight.scanner_context g' g x .callByValueSeq .callByValuePar _ _ _ _ _ htail).trans hend
    rw [hcap]
    cases n with
    | zero =>
      have hs' : sfx x p=block k++(firstPiece k++sfx x q) := by simpa [power] using hs
      have he := zero_branch g' x m' binary unary k p E' (sfx x q) b' hp unaryRule hs' hend'
      simpa only [captured,firstPiece,power,List.replicate_zero,List.flatten_nil,List.nil_append,
        length_sfx x hq] using he.symm
    | succ n =>
      have he := positive_branch g' x m' binary unary k n p E' (sfx x q) b' hb' hp binaryRule hs hend'
      simpa only [length_sfx x hq] using he.symm

/-- Both sides of a generated call start undefined at ordinary clock zero.
This is the actual seed for a recursive table induction. -/
theorem zero (g g' : MGrammar) (x : List Char) (i binary unary p : Nat)
    (E E' : List (List Char)) (b : MExp) (hp : p≤x.length)
    (sourceRule : ruleAtM g.rules i=some ⟨1,.seq scanner (.seq (.param 0) b)⟩)
    (checkRule : ruleAtM g'.rules 0=some ⟨1,checkBody⟩) :
    evV g x .callByValuePar (tblV g x .callByValuePar 0) E (.call i [argument]) p=
      evV g' x .callByValueSeq (tblV g' x .callByValueSeq 0) E' (entry binary unary) p := by
  obtain ⟨j,ha⟩ := PartialCodewordTotality.argument_total g x .callByValuePar
    (tblV g x .callByValuePar 0) (tblV_ok g x .callByValuePar 0) E p hp
  have hsource : evV g x .callByValuePar (tblV g x .callByValuePar 0) E (.call i [argument]) p=none := by
    rw [evV_call_par sourceRule rfl (by decide)]
    simp only [evParArgs,ha]
    simp only [tblV,valAt_nil]
  rw [hsource]
  have ht := PartialCodewordTotality.preflight_zero g' x p E' hp checkRule
  have hlook : evV g' x .callByValueSeq (tblV g' x .callByValueSeq 0) E'
      (look (.call 0 [runA])) p=none := by
    change evV g' x .callByValueSeq (tblV g' x .callByValueSeq 0) E' (.andP (.call 0 [runA])) p=_
    rw [CallLookahead.evV_peek,ht]
    rfl
  rw [entry,evV_seq_none hlook]

end Shallot.MacroPeg.CBV.PartialCodewordEntry
