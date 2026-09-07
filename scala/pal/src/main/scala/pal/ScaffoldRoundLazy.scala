package pal

import scala.collection.immutable.VectorMap
import scala.collection.mutable

import Expr.{TRUE, FALSE, NULL}

/** Demand-driven construction of the observable part of a packed round.
  *
  * The same virtual-node equations as scaffold_round are resolved only when a
  * query needs them. Persisted fields are closed under all old-node queries
  * reachable from acceptance. No input length or execution trace is specialized.
  *
  * Port of `scaffold_round_lazy.py`.
  */
object ScaffoldRoundLazy {

  def packRoundLazy(
      stages: Seq[Scaffold],
      inputSymbols: Option[Seq[collection.Map[Char, Expr]]] = None,
      alphabet: Option[String] = None
  ): Scaffold = {
    new DemandRoundBuilder(stages, inputSymbols, alphabet).build()
  }
}

/** Whether a slot field is a label or a pointer (Python `"label"` / `"pointer"`). */
enum FieldKind {
  case Label, Pointer
}

/** A slot field that a translation depends on. */
final case class SlotField(kind: FieldKind, slot: Int, key: String)

/** Raised by a slot lookup whose field has not been resolved yet (Python `MissingField`).
  *
  * A control-flow signal: it carries no stack trace.
  */
final class MissingField(val field: SlotField) extends RuntimeException(s"missing ${field.kind} field ${field.slot}.${field.key}") {
  override def fillInStackTrace(): Throwable = this
}

/** A `RoundBuilder` whose slot tables fill on demand, driven by acceptance. */
final class DemandRoundBuilder(
    stageSeq: Seq[Scaffold],
    inputSymbolSeq: Option[Seq[collection.Map[Char, Expr]]] = None,
    alphabetOverride: Option[String] = None
) extends RoundBuilder(stageSeq, inputSymbolSeq, alphabetOverride) {
  import FieldKind.{Label, Pointer}
  import RoundBuilder.label

  for (_ <- tags) {
    slotLabels += mutable.LinkedHashMap.empty
    slotPointers += mutable.LinkedHashMap.empty
  }

  /** One translation memo per slot (Python `self.memo.setdefault(slot, {})`). */
  private val memos = mutable.HashMap.empty[Int, java.util.IdentityHashMap[Expr, RoundValue]]
  private val pending = mutable.ArrayBuffer.empty[SlotField]
  private val requested = mutable.HashSet.empty[SlotField]

  override protected def slotLabel(slot: Int, key: String): Expr = {
    slotLabels(slot).getOrElse(key, throw new MissingField(SlotField(Label, slot, key)))
  }

  override protected def slotPointer(slot: Int, key: String): Address = {
    slotPointers(slot).getOrElse(key, throw new MissingField(SlotField(Pointer, slot, key)))
  }

  def need(kind: FieldKind, slot: Int, key: String): Unit = {
    val field = SlotField(kind, slot, key)
    if (requested.add(field)) { pending += field }
  }

  override def read(target: Address, key: String): Expr = {
    if (target.prior != NULL) {
      for (slot <- possibleTags(target.tag)) {
        if (target.tag.eqTo(slot) != FALSE) { need(Label, slot, key) }
      }
    }
    super.read(target, key)
  }

  override def follow(target: Address, key: String): Address = {
    if (target.prior != NULL) {
      for (slot <- possibleTags(target.tag)) {
        if (target.tag.eqTo(slot) != FALSE) { need(Pointer, slot, key) }
      }
    }
    super.follow(target, key)
  }

  private def resolved(field: SlotField): Boolean = {
    field.kind match {
      case Label => slotLabels(field.slot).contains(field.key)
      case Pointer => slotPointers(field.slot).contains(field.key)
    }
  }

  private def lookup(field: SlotField): RoundValue = {
    field.kind match {
      case Label => slotLabels(field.slot)(field.key)
      case Pointer => slotPointers(field.slot)(field.key)
    }
  }

  private def rootFor(slot: Int): Address = {
    if (slot == 0) { previousRoot() } else { Address(VectorMap(slot - 1 -> TRUE), NULL, zeroTag) }
  }

  /** Translate `field`, first resolving every unresolved field its translation queries. */
  def resolve(field: SlotField): RoundValue = {
    val work = mutable.ArrayBuffer(field)
    val active = mutable.HashSet(field)
    while (work.nonEmpty) {
      val current = work.last
      if (resolved(current)) {
        active -= work.remove(work.length - 1)
      } else {
        val stage = stages(current.slot)
        val memo = memos.getOrElseUpdate(current.slot, new java.util.IdentityHashMap[Expr, RoundValue]())
        try {
          current.kind match {
            case Label =>
              val value = translate(stage.labels(current.key), current.slot, rootFor(current.slot), memo)
              slotLabels(current.slot)(current.key) = value.asInstanceOf[Expr]
            case Pointer =>
              val value = translate(stage.pointers(current.key), current.slot, rootFor(current.slot), memo)
              slotPointers(current.slot)(current.key) = value.asInstanceOf[Address]
          }
          active -= work.remove(work.length - 1)
        } catch {
          case missing: MissingField =>
            if (active.contains(missing.field)) {
              throw new IllegalArgumentException("cyclic construction query in packed round", missing)
            }
            active += missing.field
            work += missing.field
        }
      }
    }
    lookup(field)
  }

  override def build(): Scaffold = {
    val accepting = stages.last.accepting
    need(Label, tags.last, accepting)
    while (pending.nonEmpty) {
      val field = pending.remove(pending.length - 1)
      val value = resolve(field)
      field.kind match {
        case Label => emitLabel(field.slot, field.key, value.asInstanceOf[Expr])
        case Pointer => emitPointer(field.slot, field.key, value.asInstanceOf[Address])
      }
    }
    new Scaffold(initial, labels, pointers, label(tags.last, accepting), alphabet)
  }
}
