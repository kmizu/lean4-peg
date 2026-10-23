import MacroPeg.CBV.PrefixInterval

namespace Shallot.MacroPeg.CBV.PrefixCounters

open RootObservation

def endpoint (equal : Nat) (position endpoint : MExp) (body : MExp) : MExp :=
  .call equal [.seq position body, endpoint]

/-- A finite parser success at a physical position can be queried for its
endpoint by the root counter grammar. Only the consumed prefix is captured. -/
theorem endpoint_success {g : MGrammar} {equal : Nat}
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    {x : List Char} {p q : Nat} (hq : q ≤ x.length)
    {body : MExp} {rest : List Char}
    (hb : SObs g .callByValuePar body (x.drop p) (some rest)) :
    SObs g .callByValuePar
      (endpoint equal (.lit (x.take p)) (.lit (x.take q)) body) x
      (if rest = x.drop q then some x else none) := by
  have hl : SObs g .callByValuePar (.lit (x.take p)) x (some (x.drop p)) :=
    ⟨_, literal_take g .callByValuePar x p, rfl⟩
  have hs := seq_ok hl hb
  obtain ⟨o, hd, ho⟩ := hs
  cases o with
  | fail => cases ho
  | ok t y =>
    have hy := Option.some.inj ho
    subst y
    obtain ⟨pref, hx⟩ := mderives_suffix hd t rest rfl
    have hn : pref.length ≤ x.length := by
      have hlen := congrArg List.length hx
      simp only [List.length_append] at hlen
      omega
    have hdrop : x.drop pref.length = rest := by
      have hh := congrArg (fun ys : List Char => ys.drop pref.length) hx
      simpa only [List.drop_left] using hh
    have hQuery := equal_arguments_obs he hn hq
      (ea := .seq (.lit (x.take p)) body) (eb := .lit (x.take q))
      (by rw [hdrop]; exact ⟨_, hd, rfl⟩)
      ⟨_, literal_take g .callByValuePar x q, rfl⟩
    have hEq : rest = x.drop q ↔ pref.length = q := by
      rw [← hdrop]
      constructor
      · intro hh
        have hlen := congrArg List.length hh
        simp only [List.length_drop] at hlen
        omega
      · rintro rfl
        rfl
    simpa only [endpoint, hEq] using hQuery

/-- An explicit parser failure gives an explicit endpoint-query failure.
No conclusion about failure is drawn from an absent source observation. -/
theorem endpoint_failure {g : MGrammar} {equal : Nat}
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    {x : List Char} {p q : Nat} {body : MExp}
    (hb : SObs g .callByValuePar body (x.drop p) none) :
    SObs g .callByValuePar
      (endpoint equal (.lit (x.take p)) (.lit (x.take q)) body) x none := by
  have hl : SObs g .callByValuePar (.lit (x.take p)) x (some (x.drop p)) :=
    ⟨_, literal_take g .callByValuePar x p, rfl⟩
  obtain ⟨o, hd, ho⟩ := seq_ok hl hb
  cases o with
  | ok _ _ => cases ho
  | fail =>
    exact ⟨_, .callParArgFail equal [] _ [_] _ x [] rfl he rfl (.nil x) hd, rfl⟩

/-- Static source literals therefore have a total, exact endpoint test. -/
theorem literal_endpoint_obs {g : MGrammar} {equal : Nat}
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x w : List Char) (p q : Nat) (hq : q ≤ x.length) :
    SObs g .callByValuePar
      (endpoint equal (.lit (x.take p)) (.lit (x.take q)) (.lit w)) x
      (if Shallot.stripPrefix? w (x.drop p) = some (x.drop q) then some x else none) := by
  cases hm : Shallot.stripPrefix? w (x.drop p) with
  | none =>
    simp only [reduceCtorEq, ite_false]
    exact endpoint_failure he ⟨_, .litFail _ _ hm, rfl⟩
  | some rest =>
    have h := endpoint_success he hq
      (body := .lit w) (p := p) ⟨_, .litOk _ _ _ hm, rfl⟩
    simpa only [hm, Option.some.injEq] using h

end Shallot.MacroPeg.CBV.PrefixCounters
