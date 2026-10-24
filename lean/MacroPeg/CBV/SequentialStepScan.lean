import MacroPeg.CBV.SequentialReturnScan

/-! Read the actual task tag and source ID to select the complete transition
kind, including a separate terminal key for an empty value stack. -/
namespace Shallot.MacroPeg.CBV.SequentialStepScan
open Complexity SequentialStack SequentialStackCodec SequentialStackPool CBVtoCBN
open SequentialReturnScan (Plan Trace lift dispatch tagged dispatch_trace lift_trace)

def exprKey : MExp → Nat
  | .seq _ _ | .alt _ _ | .notP _ | .star _ => 1
  | .call _ _ => 2
  | _ => 0

def key (c : Config) : Nat :=
  match c.task with
  | .expr _ _ src _ => exprKey src
  | .args _ _ _ _ => 3
  | .query _ _ _ _ => 4
  | .value _ => if c.stack.isEmpty then 6 else 5

def stackPlan : SequentialFrontScan.Plan := .word (.branch .done (SequentialFrontScan.frame .done))
def finish (k : Nat) : Plan := lift stackPlan (.done k)

def exprPlans (ns : List CompileNode) : List Plan :=
  (exprPool ns).map (fun src => lift (SequentialFrontScan.env .done) (finish (exprKey src)))

def valueStack : Plan := .word (.branch (.done 6) (lift (SequentialFrontScan.frame .done) (.done 5)))

def plans (ns : List CompileNode) : List Plan := [
  .word (.word (tagged (exprPlans ns))),
  lift (SequentialFrontScan.skipWords 2 (SequentialFrontScan.env (SequentialFrontScan.exprs .done))) (finish 3),
  lift (SequentialFrontScan.skipWords 3 (SequentialFrontScan.env .done)) (finish 4),
  lift (SequentialFrontScan.val .done) valueStack]

def parser (ns : List CompileNode) : Plan := tagged (plans ns)

private theorem append_trace (p : SequentialFrontScan.Plan) (held : Nat) (vs ws : List Nat) (next : Plan) (k : Nat)
    (he : SequentialFrontScan.eval p held vs = some [])
    (hn : ∀ mid, ∃ out, Trace next mid ws out k) : ∃ out, Trace (lift p next) held (vs ++ ws) out k := by
  obtain ⟨xs,mid,hh,ht⟩ := SequentialFrontScanMachine.eval_trace p held vs [] he
  simp only [List.append_nil] at hh
  subst xs
  obtain ⟨out,hn⟩ := hn mid
  exact ⟨out,lift_trace ht hn⟩

private theorem label_trace (p : SequentialFrontScan.Plan) (held : Nat) (vs : List Nat) (k : Nat)
    (he : SequentialFrontScan.eval p held vs = some []) : ∃ out, Trace (lift p (.done k)) held vs out k := by
  simpa using append_trace p held vs [] (.done k) k he (fun mid => ⟨mid,.done k mid⟩)

private theorem stack_trace (ns : List CompileNode) (K : List SequentialStack.Frame) (held k : Nat) :
    ∃ out, Trace (finish k) held (K.length :: SequentialFront.suffixCode ns (K.take 1)) out k := by
  apply label_trace
  cases K with
  | nil => simp [stackPlan,SequentialFront.suffixCode,SequentialFrontScan.eval]
  | cons f K =>
    simpa [stackPlan,SequentialFront.suffixCode,SequentialFrontScan.eval] using
      SequentialFrontScan.frame_correct ns f .done K.length [] [] (fun _ => rfl)

private theorem value_trace (ns : List CompileNode) (K : List SequentialStack.Frame) (held : Nat) :
    ∃ out, Trace valueStack held (K.length :: SequentialFront.suffixCode ns (K.take 1)) out (if K.isEmpty then 6 else 5) := by
  cases K with
  | nil => exact ⟨0,.word (.zero (.done 6 0))⟩
  | cons f K =>
    obtain ⟨out,ht⟩ := label_trace (SequentialFrontScan.frame .done) K.length (writeFrame ns f) 5
      (by simpa using SequentialFrontScan.frame_correct ns f .done K.length [] [] (fun _ => rfl))
    exact ⟨out,by simpa [valueStack,SequentialFront.suffixCode] using Trace.word (Trace.positive ht)⟩

theorem parser_trace (ns : List CompileNode) (c : Config) (hpool : TaskOK ns c.task) (held : Nat) :
    ∃ out, Trace (parser ns) held
      (SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c)) out (key c) := by
  obtain ⟨t,K⟩ := c
  have hhead : (K.take 1).length+(K.drop 1).length = K.length := by
    have hh := congrArg List.length (List.take_append_drop 1 K)
    simpa only [List.length_append] using hh
  have hlen : min 1 K.length+(K.length-1)=K.length := by simpa using hhead
  cases t with
  | expr m E src p =>
    have hget : (exprPlans ns)[exprId ns src]? = some (lift (SequentialFrontScan.env .done) (finish (exprKey src))) := by
      simp only [exprPlans,List.getElem?_map,exprId]
      rw [get_idxOf hpool.mem]
      rfl
    obtain ⟨out,ht⟩ := append_trace (SequentialFrontScan.env .done) 0 (writeEnv E)
      (K.length :: SequentialFront.suffixCode ns (K.take 1)) (finish (exprKey src)) (exprKey src)
      (by simpa using SequentialFrontScan.env_correct E .done 0 [] [] (fun _ => rfl))
      (fun mid => stack_trace ns K mid (exprKey src))
    have hx : Trace (.word (.word (tagged (exprPlans ns)))) 0
        ([m,p,exprId ns src] ++ writeEnv E ++ (K.length :: SequentialFront.suffixCode ns (K.take 1))) out (exprKey src) :=
      Trace.word (Trace.word (Trace.word (dispatch_trace (exprPlans ns) (exprId ns src) _ hget ht)))
    exact ⟨out,by simpa [parser,plans,tagged,key,SequentialFront.prefixCode,SequentialFront.front,
      SequentialFront.tail,writeTask,writeExpr,List.append_assoc,hlen] using (Trace.word (held := held) (dispatch_trace (plans ns) 0 _ rfl hx))⟩
  | args m E es p =>
    obtain ⟨out,ht⟩ := append_trace
      (SequentialFrontScan.skipWords 2 (SequentialFrontScan.env (SequentialFrontScan.exprs .done))) 0
      ([m,p] ++ writeEnv E ++ writeExprs ns es)
      (K.length :: SequentialFront.suffixCode ns (K.take 1)) (finish 3) 3
      (by
        simpa [List.append_assoc] using
          (SequentialFrontScan.skip_correct [m,p] _ 0 _ []
            (fun h => SequentialFrontScan.env_correct E _ h _ []
              (fun h => SequentialFrontScan.exprs_correct ns es .done h [] [] (fun _ => rfl)))))
      (fun mid => stack_trace ns K mid 3)
    exact ⟨out,by simpa [parser,plans,tagged,key,SequentialFront.prefixCode,SequentialFront.front,
      SequentialFront.tail,writeTask,List.append_assoc,hlen] using Trace.word (held := held) (dispatch_trace (plans ns) 1 _ rfl ht)⟩
  | query m i E p =>
    obtain ⟨out,ht⟩ := append_trace (SequentialFrontScan.skipWords 3 (SequentialFrontScan.env .done)) 0
      ([m,i,p] ++ writeEnv E) (K.length :: SequentialFront.suffixCode ns (K.take 1)) (finish 4) 4
      (by
        simpa using (SequentialFrontScan.skip_correct [m,i,p] _ 0 _ []
          (fun h => SequentialFrontScan.env_correct E .done h [] [] (fun _ => rfl))))
      (fun mid => stack_trace ns K mid 4)
    exact ⟨out,by simpa [parser,plans,tagged,key,SequentialFront.prefixCode,SequentialFront.front,
      SequentialFront.tail,writeTask,List.append_assoc,hlen] using Trace.word (held := held) (dispatch_trace (plans ns) 2 _ rfl ht)⟩
  | value v =>
    obtain ⟨out,ht⟩ := append_trace (SequentialFrontScan.val .done) 0 (writeValue v)
      (K.length :: SequentialFront.suffixCode ns (K.take 1)) valueStack (if K.isEmpty then 6 else 5)
      (by simpa using SequentialFrontScan.val_correct v .done 0 [] [] (fun _ => rfl))
      (fun mid => value_trace ns K mid)
    exact ⟨out,by simpa [parser,plans,tagged,key,SequentialFront.prefixCode,SequentialFront.front,
      SequentialFront.tail,writeTask,List.append_assoc,hlen] using Trace.word (held := held) (dispatch_trace (plans ns) 3 _ rfl ht)⟩

end Shallot.MacroPeg.CBV.SequentialStepScan
