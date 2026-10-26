import MacroPeg.CBV.SequentialCanonicalQueries
import MacroPeg.CBV.SequentialProbeTriangle

namespace Shallot.MacroPeg.CBV.CanonicalQueryExamples

open SequentialCanonicalQueries (key run)
open SequentialProbeTriangle (grammar input request frameRequest row outerTrace targets)

abbrev Key := Nat × SequentialSpanRecompute.Env × Nat
def targetKey : Key := (1,[(0,0),(0,0)],1)
def frameKey (n m : Nat) : Key := (0,[(m+n+2,n+2)],n+2)

def cache (n : Nat) : List Key := (List.range (n+1)).map (frameKey n) ++ [targetKey]

theorem target_key (m r : Nat) :
    key grammar (request m r).rule (request m r).env (request m r).cursor = targetKey := by
  simp [key, request, grammar, ruleAtM, targetKey, CaptureReadSupport.canonical,
    CaptureReadSupport.reads, List.mapIdx_cons]

theorem frame_key (n m : Nat) :
    key grammar (frameRequest n m).rule (frameRequest n m).env (frameRequest n m).cursor = frameKey n m := by
  simp [key, frameRequest, grammar, ruleAtM, frameKey, CaptureReadSupport.canonical,
    CaptureReadSupport.reads, CaptureReadSupport.argumentReads, SequentialProbeTriangle.body,
    SequentialProbeTriangle.inner, SequentialProbeTriangle.scan, MExp.andP, List.mapIdx_cons]

/-- The quadratically many distinct retained-word requests use one canonical
target key. This statement does not reduce the number of calls in the trace. -/
theorem target_keys_one (n : Nat) : ∀ req ∈ targets n,
    key grammar req.rule req.env req.cursor = targetKey := by
  intro req hreq
  obtain ⟨m,r,hmr,rfl⟩ := (SequentialProbeTriangle.targets_mem n req).mp hreq
  exact target_key m r

theorem cache_size (n : Nat) : (cache n).length=n+2 := by simp [cache]

private theorem frame_injective (n : Nat) {a b : Nat} (h : frameKey n a=frameKey n b) : a=b := by
  simp only [frameKey, Prod.mk.injEq, List.cons.injEq, Prod.mk.injEq] at h
  omega

theorem cache_nodup (n : Nat) : (cache n).Nodup := by
  simp only [cache, List.Nodup, List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · exact List.Pairwise.map (R := fun a b : Nat => a≠b) _
      (fun a b hab he => hab (frame_injective n he)) List.nodup_range
  · intro a ha b hb he
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_singleton] at hb
    have hh := congrArg Prod.fst (he.trans hb)
    simp [frameKey,targetKey] at hh

/-- At this acyclic witness, caller rows are evaluated at clock 2 and target
rows at clock 1. Keys here omit that fixed external table-layer index. -/
theorem cache_covers_trace (n : Nat) :
    ∀ req ∈ (SequentialProbeTrace.run grammar (input n) 2 SequentialProbeTriangle.start).2,
      key grammar req.rule req.env req.cursor ∈ cache n := by
  rw [SequentialProbeTriangle.run_formula]
  intro req hreq
  obtain ⟨m,hm,hr⟩ := List.mem_flatMap.mp hreq
  simp only [List.mem_reverse, List.mem_range] at hm
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [frame_key]
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨m,by simp; omega,rfl⟩
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr
    rw [target_key]
    exact List.mem_append_right _ (by simp)

def recursive : MGrammar := ⟨[⟨3,
  .alt (.seq (.chr '#') (.seq (.param 2) (.param 0)))
    (.seq (.chr '!')
      (.seq (.call 0 [.seq (.param 0) (.param 0), .chr '?', .seq (.param 2) (.param 2)])
        (.seq (.param 2) (.param 0))))⟩]⟩

/-- The unused middle capture is erased at both entries, while its actual
still consumes ~ or ?. Fresh child aa/bb and parent a/b stay independent. -/
theorem recursive_live_fields_and_unused_gap :
    let x := "a~b!aa?bb#bbaaba".toList
    run recursive x 2 [] (.call 0 [.chr 'a', .chr '~', .chr 'b']) x.length = some (some 0) ∧
    CaptureReadSupport.canonical recursive.rules[0].body [(16,15),(15,14),(14,13)] =
      [(16,15),(0,0),(14,13)] ∧
    CaptureReadSupport.canonical recursive.rules[0].body [(12,10),(10,9),(9,7)] =
      [(12,10),(0,0),(9,7)] := by decide +kernel

theorem actual_consumption_is_preserved :
    let g : MGrammar := ⟨[⟨1,.eps⟩]⟩
    run g ['a'] 1 [] (.call 0 [.chr 'a']) 1 = some (some 0) ∧
    run g ['a'] 1 [] (.call 0 [.chr 'b']) 1 = some none ∧
    run g ['a'] 1 [] (.call 0 [.eps]) 1 = some (some 1) := by decide +kernel

theorem undefined_actual_is_preserved (x : List Char) (m : Nat) :
    run ⟨[⟨1,.eps⟩]⟩ x m [] (.call 0 [.star .eps]) x.length = none := by
  rw [SequentialCanonicalQueries.run_correct _ _ _ [] (by intro span hs; cases hs) _ _ (Nat.le_refl _)]
  simp [evV, evSeqArgs, evStar, ruleAtM]

theorem invalid_calls_keep_preflight :
    let g : MGrammar := ⟨[⟨1,.eps⟩]⟩
    run g ['a'] 1 [] (.call 4 [.star .eps]) 1 = some none ∧
    run g ['a'] 1 [] (.call 0 [.star .eps,.eps]) 1 = some none := by decide +kernel

/-- A parameter read by an actual remains relevant even when the target
body ignores every formal parameter. -/
theorem actual_reads_cannot_be_dropped :
    CaptureReadSupport.reads (.call 0 [.param 0]) = [0] ∧
    let g : MGrammar := ⟨[⟨1,.eps⟩]⟩
    run g ['a'] 1 [(1,0)] (.call 0 [.param 0]) 1 = some (some 0) ∧
    run g ['a'] 1 [(0,0)] (.call 0 [.param 0]) 1 = some (some 1) := by decide +kernel

end Shallot.MacroPeg.CBV.CanonicalQueryExamples
