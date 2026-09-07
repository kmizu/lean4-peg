package pal

import scala.annotation.tailrec

/** Coroutine support for the Python generators of `gs_heads.py` and `gs_events.py`.
  *
  * The Python originals are generators driven by `send`: the generator yields an
  * event (a head instruction or an indexed operation), the driver answers with the
  * outcome of a test (`True`/`False`) or `None` for a command, and `yield from`
  * delegates to a sub-generator whose return value becomes the value of the
  * `yield from` expression.
  *
  * The port encodes each generator as an explicit state machine (a [[Generator]]
  * subclass). The generator body is split at every textual `yield` / `yield from`
  * into a *site*; `step` receives the response to the yield at the current site,
  * runs the straight-line Python code up to the next suspension point and reports
  * it as an [[Action]]. Delegation (`yield from`) is handled once, in
  * [[Generator.send]], so the subclasses only ever describe their own frame.
  *
  * This explicit encoding was chosen over threads or a monadic encoding because
  * `gs_heads.compile_controller` needs to *inspect* the suspended generator stack
  * (`_control_key` reads `co_name`, `f_lasti` and `f_locals` of every frame in the
  * `gi_yieldfrom` chain). A [[Frame]] is exactly that triple: generator name,
  * suspension site and the currently bound locals. Keeping the same granularity as
  * CPython (one site per textual yield, locals present only once assigned) makes
  * the construction-state counts of the Python compiler reproducible, not only the
  * minimized tables.
  */
object Coroutine {

  /** A frozen Python local: `_freeze` only admits `None`/bool/int/str (and tuples
    * of those, which never occur in the controllers). `None` never occurs either.
    */
  type Local = Int | Boolean | String

  /** One suspended generator frame, as seen by `_control_key`. */
  final case class Frame(name: String, site: Int, locals: Vector[(String, Local)])
}

/** What the driver receives from `send`. */
sealed trait Step[+E, +R]

/** The generator suspended at a `yield` of `event`. */
final case class Yielded[E](event: E) extends Step[E, Nothing]

/** The generator ran to `return value` (Python raises `StopIteration(value)`). */
final case class Returned[R](value: R) extends Step[Nothing, R]

/** What a frame's `step` asks the driver to do next. Invariant in both
  * parameters (a [[Generator]] is invariant in its event type); the type
  * arguments are inferred from the expected `Action[E, R]` of `step`.
  */
sealed trait Action[E, R]

object Action {

  /** Suspend at a `yield event`. */
  final case class Emit[E, R](event: E) extends Action[E, R]

  /** Suspend inside `yield from child` until `child` returns. */
  final case class Call[E, R](child: Generator[E, ?]) extends Action[E, R]

  /** `return value`. */
  final case class Return[E, R](value: R) extends Action[E, R]
}

/** A Python generator as an explicit state machine.
  *
  * @param name the Python function name (`co_name`), part of the control key
  * @tparam E the yielded event type
  * @tparam R the return type of the generator
  */
abstract class Generator[E, R](val name: String) {
  import Action.*

  /** The suspension site (index of the textual `yield`/`yield from`), 0 before
    * the first activation. Subclasses assign it in `step`.
    */
  protected var site: Int = 0

  private var delegate: Option[Generator[E, ?]] = None
  private var outcome: Option[R] = None

  /** The return value, available once `send` returned [[Returned]]. Parents read
    * their child's result here after a `yield from` completed.
    */
  def result: R = outcome.getOrElse(throw new IllegalStateException(s"$name has not returned"))

  /** The currently bound Python locals of this frame (any order). */
  def locals: Vector[(String, Coroutine.Local)] = Vector.empty

  /** The current suspension site, for observers. */
  def currentSite: Int = site

  /** Resume with the response to the current suspension and run to the next one.
    * `response` is `None` after a command or on the first activation, and the
    * test outcome after a test.
    */
  protected def step(response: Option[Boolean]): Action[E, R]

  /** Python's `generator.send(response)`; the first activation is `send(None)`. */
  final def send(response: Option[Boolean]): Step[E, R] = {
    delegate match {
      case Some(child) =>
        resumeChild(child, response) match {
          case Some(event) => Yielded(event)
          case None =>
            delegate = None
            advance(None)
        }
      case None => advance(response)
    }
  }

  /** Resume a delegate; `None` once it returned. */
  private def resumeChild[C](child: Generator[E, C], response: Option[Boolean]): Option[E] = {
    child.send(response) match {
      case Yielded(event) => Some(event)
      case Returned(_) => None
    }
  }

  @tailrec
  private def advance(response: Option[Boolean]): Step[E, R] = {
    step(response) match {
      case Emit(event) => Yielded(event)
      case Return(value) =>
        outcome = Some(value)
        Returned(value)
      case Call(child) =>
        resumeChild(child, None) match {
          case Some(event) =>
            delegate = Some(child)
            Yielded(event)
          case None => advance(None)
        }
    }
  }

  /** The `gi_yieldfrom` chain, outermost first, with locals sorted by name as in
    * `_control_key`.
    */
  final def frames: List[Coroutine.Frame] = {
    val own = Coroutine.Frame(name, site, locals.sortBy(_._1))
    own :: delegate.map(_.frames).getOrElse(Nil)
  }
}
