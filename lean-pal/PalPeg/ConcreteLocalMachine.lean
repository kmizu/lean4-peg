import PalPeg.LocalQueueInit
import PalPeg.LocalViewCells

/-!
# The concrete local machine

Entry point of the concrete persistent local machine for `obligation_localRealization`.
So far: the Hood–Melville queue of an input view.

* `PalPeg.LocalQueueLayout` — finite observation, sealed layout, the sub-step on cells;
* `PalPeg.LocalQueueMachine` — stack tapes, `queueRule`, `QueueRep`, `queueRule_sound`;
* `PalPeg.LocalQueueLength` — the schedule of `snoc` / `tail`, the lazy length counter;
* `PalPeg.LocalQueueMicro` — the micro-programmed machine, `MicroRep`, `microRule_sound`.
* `PalPeg.LocalQueueProgram` — `RTQueue.snoc` / `tail` as lists of micro-operations, the machine
  with a program counter, `programRun_snoc` / `programRun_tail`;
* `PalPeg.LocalQueueInit` — the first step, from blank tapes to the empty queue (`programInit`);
* `PalPeg.LocalViewCells` — the content of a view is the sentinel followed by letters, so the
  emptiness of `back` is readable from the focus (`back_nil_iff_focus_none`).
-/
