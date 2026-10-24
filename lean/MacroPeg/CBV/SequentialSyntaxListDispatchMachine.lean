import MacroPeg.CBV.SequentialExpressionDispatchMachine

/-! A source-fixed decoder for inline syntax lists behind arbitrary unary
headers. Each field inspection restores the complete source before continuing. -/
namespace Shallot.MacroPeg.CBV.SequentialSyntaxListDispatchMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine

def parse (ns : List CBVtoCBN.CompileNode) (saved : Nat) (next : List MExp → LProg 8) :
    Nat → List MExp → LProg 8
  | 0,done => next done
  | fuel+1,done => SequentialTagDispatchMachine.program 2 1 (saved+1+done.length)
      (SequentialStackPool.exprPool ns).length (fun id => match (SequentialStackPool.exprPool ns)[id]? with
        | some a => parse ns saved next fuel (done ++ [a])
        | none => skipP 2)

def program (ns : List CBVtoCBN.CompileNode) (saved bound : Nat) (next : List MExp → LProg 8) : LProg 8 :=
  SequentialTagDispatchMachine.program 2 1 saved bound (fun n => parse ns saved next n [])

theorem parse_runs (ns : List CBVtoCBN.CompileNode) (next : List MExp → LProg 8)
    (done es : List MExp) (header tail : List Nat) (L M : Lists 8) {B T : Nat}
    (hpool : ∀ a ∈ done ++ es, a ∈ SequentialStackPool.exprPool ns)
    (hctrl : L 2=tail ++ blocks (header ++ [(done ++ es).length] ++
      (done ++ es).map (SequentialStackCodec.exprId ns)))
    (h1 : L 1=[]) (hL : LenOK B L) (hp : Runs (LenOK B) (next (done ++ es)) L M T) :
    ∃ U, Runs (LenOK B) (parse ns header.length next es.length done) L M U := by
  induction es generalizing done with
  | nil =>
    refine ⟨T,?_⟩
    simpa only [List.append_nil,List.length_nil,parse] using hp
  | cons a es ih =>
    have he : (done ++ [a]) ++ es=done ++ a :: es := by simp only [List.append_assoc,List.singleton_append]
    obtain ⟨U,hu⟩ := ih (done ++ [a]) (by simpa only [he] using hpool)
      (by simpa only [he] using hctrl) (by simpa only [he] using hp)
    have ha : a ∈ SequentialStackPool.exprPool ns := hpool a (by simp)
    have hget : (SequentialStackPool.exprPool ns)[SequentialStackCodec.exprId ns a]?=some a := get_idxOf ha
    let nextBranch := fun (id : Nat) => match (SequentialStackPool.exprPool ns)[id]? with
      | some b => parse ns header.length next es.length (done ++ [b])
      | none => skipP 2
    have hb : Runs (LenOK B) (nextBranch (SequentialStackCodec.exprId ns a)) L M U := by
      simpa only [nextBranch,hget] using hu
    let saved := header ++ [(done ++ a :: es).length] ++ done.map (SequentialStackCodec.exprId ns)
    let C := (tail ++ blocks (es.map (SequentialStackCodec.exprId ns))) ++ [0]
    have hsrc : L 2=C ++ unary (SequentialStackCodec.exprId ns a) ++ blocks saved := by
      rw [hctrl]
      simp only [C,saved,List.map_append,List.map_cons,blocks_append,blocks_cons,
        show blocks []=[] from rfl,List.nil_append,List.append_assoc]
    obtain ⟨V,hv⟩ := SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
      saved (SequentialStackPool.exprPool ns).length (SequentialStackCodec.exprId ns a)
      (Nat.le_of_lt (List.idxOf_lt_length_of_mem ha)) C nextBranch L M hsrc
      (by rw [lastSym_append]; rfl) h1 hL hb
    have hlen : saved.length=header.length+1+done.length := by
      simp [saved]
      omega
    rw [hlen] at hv
    refine ⟨V,?_⟩
    simpa only [parse,List.length_cons] using hv

/-- The result is the selected continuation's actual bounded run. Only the
header count, source pool, bound, and continuation family are code parameters. -/
theorem program_runs (ns : List CBVtoCBN.CompileNode) (bound : Nat) (next : List MExp → LProg 8)
    (es : List MExp) (header tail : List Nat) (L M : Lists 8) {B T : Nat}
    (hlen : es.length ≤ bound) (hpool : ∀ a ∈ es, a ∈ SequentialStackPool.exprPool ns)
    (hctrl : L 2=tail ++ blocks (header ++ [es.length] ++ es.map (SequentialStackCodec.exprId ns)))
    (h1 : L 1=[]) (hL : LenOK B L) (hp : Runs (LenOK B) (next es) L M T) :
    ∃ U, Runs (LenOK B) (program ns header.length bound next) L M U := by
  obtain ⟨U,hu⟩ := parse_runs ns next [] es header tail L M (by simpa using hpool)
    (by simpa using hctrl) h1 hL (by simpa using hp)
  let C := (tail ++ blocks (es.map (SequentialStackCodec.exprId ns))) ++ [0]
  have hsrc : L 2=C ++ unary es.length ++ blocks header := by
    rw [hctrl]
    simp only [C,blocks_append,blocks_cons,show blocks []=[] from rfl,List.nil_append,List.append_assoc]
  exact SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide)
    header bound es.length hlen C (fun n => parse ns header.length next n []) L M hsrc
    (by rw [lastSym_append]; rfl) h1 hL hu

theorem finite_alphabet (ns : List CBVtoCBN.CompileNode) (saved bound : Nat) (next : List MExp → LProg 8) :
    ∃ E, 0x110001 ≤ E ∧ (program ns saved bound next).compile.SymOK (E+4) := by
  obtain ⟨E,_hE,hc⟩ := LProg.exists_constOK (program ns saved bound next)
  exact ⟨max E 0x110001,Nat.le_max_right _ _,compile_symOK _ _
    (LProg.ConstOK.mono (Nat.le_max_left E 0x110001) hc)⟩

end Shallot.MacroPeg.CBV.SequentialSyntaxListDispatchMachine
