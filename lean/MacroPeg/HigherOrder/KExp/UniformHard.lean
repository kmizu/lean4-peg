import MacroPeg.HigherOrder.KExp.LamFree

/-!
# The uniform problem for order `j` is `j`-EXPTIME-hard

The reduction of `kexp_hard` fixes the grammar `gT M (j - 1)` per machine; its serialization is a constant. The
template `uT` writes that constant, then the encoding `encT` with every character serialized (`mapTok`), then the end
of the string. So `w ↦ serIn (gT M (j - 1)) (startT (j - 1)) (encChars m w)` is computable in polynomial time
(`tmpl_polytime`), and `w ∈ L` iff the instance is in `UMPEG j` (`uniform_hard`).
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Levels
open Shallot.MacroPeg.Tableau

/-! ## Rewriting the tokens of a template -/

/-- Replace every token `t` by the tokens `φ t`. -/
def mapTok (φ : Nat → List Nat) : Tmpl → Tmpl
  | .nil => .nil
  | .tok t => Tmpl.seqs ((φ t).map .tok)
  | .name ps => .name ps
  | .seq a b => .seq (mapTok φ a) (mapTok φ b)
  | .forR i b body => .forR i b (mapTok φ body)
  | .ite c a b => .ite c (mapTok φ a) (mapTok φ b)

theorem denote_seqs_tok (e : TEnv) (l : List Nat) : (Tmpl.seqs (l.map .tok)).denote e = l := by
  rw [Tmpl.denote_seqs]; induction l <;> simp_all [Tmpl.denote]

theorem loops_seqs_tok : ∀ l : List Nat, (Tmpl.seqs (l.map .tok)).loops = []
  | [] => rfl
  | _ :: l => by simp [Tmpl.seqs, Tmpl.loops, loops_seqs_tok l]

theorem wf_seqs_tok (nc : Nat) : ∀ l : List Nat, (Tmpl.seqs (l.map .tok)).WF nc
  | [] => trivial
  | _ :: l => ⟨trivial, wf_seqs_tok nc l⟩

theorem small_seqs_tok (Z : Nat) : ∀ l : List Nat, (∀ t ∈ l, t < 16) → (Tmpl.seqs (l.map .tok)).Small Z
  | [], _ => trivial
  | t :: l, h => ⟨h t List.mem_cons_self, small_seqs_tok Z l (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem mapTok_denote (φ : Nat → List Nat) : ∀ (t : Tmpl), Plain t → ∀ e, (mapTok φ t).denote e = (t.denote e).flatMap φ
  | .nil, _, _ => rfl
  | .tok t, _, e => by simp [mapTok, denote_seqs_tok, Tmpl.denote]
  | .name _, hp, _ => hp.elim
  | .seq a b, hp, e => by simp [mapTok, Tmpl.denote, mapTok_denote φ a hp.1, mapTok_denote φ b hp.2]
  | .forR i b body, hp, e => by
    simp only [mapTok, Tmpl.denote, List.flatMap_assoc]
    congr 1; funext v; exact mapTok_denote φ body hp _
  | .ite c a b, hp, e => by
    simp only [mapTok, Tmpl.denote]
    split
    · exact mapTok_denote φ a hp.1 e
    · exact mapTok_denote φ b hp.2 e

theorem mapTok_loops (φ : Nat → List Nat) : ∀ t : Tmpl, (mapTok φ t).loops = t.loops
  | .nil | .name _ => rfl
  | .tok _ => loops_seqs_tok _
  | .seq a b | .ite _ a b => by simp [mapTok, Tmpl.loops, mapTok_loops φ a, mapTok_loops φ b]
  | .forR _ _ body => by simp [mapTok, Tmpl.loops, mapTok_loops φ body]

theorem mapTok_WF (φ : Nat → List Nat) (nc : Nat) : ∀ t : Tmpl, t.WF nc → (mapTok φ t).WF nc
  | .nil, h => h
  | .name _, h => h
  | .tok _, _ => wf_seqs_tok nc _
  | .seq a b, h => ⟨mapTok_WF φ nc a h.1, mapTok_WF φ nc b h.2⟩
  | .forR _ _ body, h => ⟨h.1, by rw [mapTok_loops]; exact h.2.1, mapTok_WF φ nc body h.2.2⟩
  | .ite _ a b, h => ⟨h.1, mapTok_WF φ nc a h.2.1, mapTok_WF φ nc b h.2.2⟩

theorem mapTok_small (φ : Nat → List Nat) (hφ : ∀ x, ∀ y ∈ φ x, y < 16) (Z : Nat) :
    ∀ t : Tmpl, t.Small Z → (mapTok φ t).Small Z
  | .nil, h => h
  | .name _, h => h
  | .tok t, _ => small_seqs_tok Z _ (hφ t)
  | .seq a b, h => ⟨mapTok_small φ hφ Z a h.1, mapTok_small φ hφ Z b h.2⟩
  | .forR _ _ body, h => ⟨h.1, mapTok_small φ hφ Z body h.2⟩
  | .ite _ a b, h => ⟨h.1, mapTok_small φ hφ Z a h.2.1, mapTok_small φ hφ Z b h.2.2⟩

/-! ## The template of the uniform reduction -/

/-- A token of `encT`, serialized as a character of a string. -/
def charTok (t : Nat) : List Nat := 1 :: serChar (tokChar t)

theorem charTok_lt (t : Nat) : ∀ y ∈ charTok t, y < 16 := by
  intro y hy
  simp only [charTok, List.mem_cons] at hy
  rcases hy with h | h
  · omega
  · exact serNat_lt _ y h

theorem serStr_eq : ∀ x : List Char, serStr x = x.flatMap (fun c => 1 :: serChar c) ++ [0]
  | [] => rfl
  | c :: x => by simp [serStr, serStr_eq x]

/-- The instance for machine `M`: the grammar and start (constant), then the encoding as a string. -/
def uT (g : HGrammar) (s : HExp) : Tmpl :=
  .seq (Tmpl.seqs ((serTys (g.rules.map HRule.ty) ++ (serBodies (g.rules.map HRule.body) ++ serE s)).map .tok))
    (.seq (mapTok charTok encT) (.tok 0))

theorem uT_WF (g : HGrammar) (s : HExp) : (uT g s).WF 4 :=
  ⟨wf_seqs_tok 4 _, mapTok_WF charTok 4 encT encT_WF, trivial⟩

theorem uT_small (g : HGrammar) (s : HExp) (Z : Nat) : (uT g s).Small Z := by
  refine ⟨small_seqs_tok Z _ (fun t ht => ?_), mapTok_small charTok charTok_lt Z encT (encT_small Z), show 0 < 16 by decide⟩
  rcases List.mem_append.1 ht with h | h
  · exact serTys_lt _ t h
  rcases List.mem_append.1 h with h | h
  · exact serBodies_lt _ t h
  · exact serE_lt _ t h

theorem uT_denote (g : HGrammar) (s : HExp) (w : List Bool) (S T : Nat) (ctr : Nat → Nat) (hn : w.length ≤ S) :
    (uT g s).denote ⟨w, S, T, ctr⟩ = serIn g s (encChars S w) := by
  have hp : Plain encT := by simp [encT, bitSiteT, inSiteT, codeT, Plain]
  simp only [uT, Tmpl.denote, denote_seqs_tok, mapTok_denote charTok encT hp, serIn, serStr_eq,
    ← encT_denote w S T ctr hn, List.flatMap_map, List.append_assoc]
  rfl

/-! ## The reduction -/

/-- **The uniform problem for order `j ≥ 1` is `j`-EXPTIME-hard**: every `j`-EXPTIME language reduces in polynomial
time to `UMPEG j`. -/
theorem uniform_hard {j : Nat} (hj : 1 ≤ j) {L : Lang} (hL : KEXP j L) : Reduces L (UMPEG j) := by
  obtain ⟨kt, M, T, c, d, hT, hdec, htb⟩ := hL
  let g := gT M (j - 1)
  let s := startT (j - 1)
  refine ⟨tmplBits (uT g s) (c + 1) (d + 1), tmpl_polytime _ (uT_WF g s) (uT_small g s) _ _, fun w => ?_⟩
  have hnm := (sites_large c d w.length).2
  have hden : tmplBits (uT g s) (c + 1) (d + 1) w =
      toBits (serIn g s (encChars (rS (c + 1) (d + 1) w.length) w)) := by
    unfold tmplBits encEnv
    rw [uT_denote g s w _ 0 _ (Nat.le_of_lt hnm)]
  rw [hden, umpeg_toBits, kexp_reduction hj hT hdec htb w]
  unfold MPEG
  rw [decode_encBits _ _ w (Nat.le_of_lt hnm)]
  have hord : GOrd j g s := by
    have := gT_GOrd M (j - 1)
    rwa [show j - 1 + 1 = j by omega] at this
  refine ⟨fun h => ⟨gT_wellTyped M _, hord, startT_hasTy M _, h⟩, fun h => h.2.2.2⟩

end Shallot.MacroPeg.KExp
