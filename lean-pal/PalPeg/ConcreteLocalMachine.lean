import PalPeg.LocalQueueMicro

/-!
# The concrete local machine

Entry point of the concrete persistent local machine for `obligation_localRealization`.
So far: the Hood–Melville queue of an input view.

* `PalPeg.LocalQueueLayout` — finite observation, sealed layout, the sub-step on cells;
* `PalPeg.LocalQueueMachine` — stack tapes, `queueRule`, `QueueRep`, `queueRule_sound`;
* `PalPeg.LocalQueueLength` — the schedule of `snoc` / `tail`, the lazy length counter;
* `PalPeg.LocalQueueMicro` — the micro-programmed machine, `MicroRep`, `microRule_sound`.
-/
