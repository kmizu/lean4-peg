package pal

import java.io.{BufferedInputStream, FileInputStream}
import java.nio.charset.StandardCharsets
import java.nio.file.Path
import java.util.Arrays

/** `GrammarScc` / `GrammarClosure` が実物の文法（13,248,052 規則、672 MB、bytecode
  * 210,830,100 int、辺 72,376,872 本）を Python 版と同じメモリ形状で扱うための道具。
  * Python は `array('i')` / `array('b')` とファイルの逐次読みを使う。ここでも
  * ボクシングしない可変長配列と、'\n' だけで区切る Latin-1 の行読みを用意する。
  */
object GrammarTools {

  /** Growth policy shared by the vectors: ×1.25 like CPython's `array`, so the transient
    * peak while growing stays close to the final size (doubling would spike to 3×).
    */
  private def grown(length: Int): Int = math.max(16, length + (length >> 2) + 1)

  /** Python の `array('i')`：ボクシングしない可変長 Int 配列。 */
  final class IntVec(initialCapacity: Int = 16) {
    private var data = new Array[Int](math.max(initialCapacity, 1))
    private var count = 0

    def size: Int = count
    def isEmpty: Boolean = count == 0
    def nonEmpty: Boolean = count != 0

    def apply(i: Int): Int = {
      if (i >= count) { throw new IndexOutOfBoundsException(s"$i >= $count") }
      data(i)
    }

    def update(i: Int, v: Int): Unit = {
      if (i >= count) { throw new IndexOutOfBoundsException(s"$i >= $count") }
      data(i) = v
    }

    def +=(v: Int): Unit = {
      if (count == data.length) { data = Arrays.copyOf(data, grown(data.length)) }
      data(count) = v
      count += 1
    }

    def ++=(other: IntVec): Unit = {
      val needed = count + other.count
      if (needed > data.length) { data = Arrays.copyOf(data, math.max(grown(data.length), needed)) }
      System.arraycopy(other.data, 0, data, count, other.count)
      count = needed
    }

    /** Python の `[x] + rest` に相当：位置 `pos` に挿入して後続をずらす。 */
    def insert(pos: Int, v: Int): Unit = insertRepeated(pos, v, 1)

    /** `[x] * times + rest`：同じ値を `times` 個まとめて挿入する（ずらしは 1 回）。 */
    def insertRepeated(pos: Int, v: Int, times: Int): Unit = {
      val needed = count + times
      if (needed > data.length) { data = Arrays.copyOf(data, math.max(grown(data.length), needed)) }
      System.arraycopy(data, pos, data, pos + times, count - pos)
      Arrays.fill(data, pos, pos + times, v)
      count = needed
    }

    def last: Int = data(count - 1)

    def pop(): Int = {
      count -= 1
      data(count)
    }

    def clear(): Unit = { count = 0 }

    def toArray: Array[Int] = Arrays.copyOf(data, count)
  }

  /** Python の `array('b')`：ボクシングしない可変長 Byte 配列。 */
  final class ByteVec(initialCapacity: Int = 16) {
    private var data = new Array[Byte](math.max(initialCapacity, 1))
    private var count = 0

    def size: Int = count
    def apply(i: Int): Byte = {
      if (i >= count) { throw new IndexOutOfBoundsException(s"$i >= $count") }
      data(i)
    }

    def +=(v: Byte): Unit = {
      if (count == data.length) { data = Arrays.copyOf(data, grown(data.length)) }
      data(count) = v
      count += 1
    }

    /** `sum(array)` for 0/1 flags. */
    def countNonZero: Int = {
      var total = 0
      var i = 0
      while (i < count) { if (data(i) != 0) { total += 1 }; i += 1 }
      total
    }
  }

  /** Python の `ids = {}; names = []`：名前 → 出現順の稠密な id と、その逆引き。
    * open addressing（線形探索）で値をボクシングしない。
    */
  final class StringIndex(initialCapacity: Int = 1 << 16) {
    private var keys = new Array[String](tableSize(initialCapacity))
    private var values = new Array[Int](keys.length)
    private var names = new Array[String](math.max(initialCapacity, 16))
    private var count = 0

    private def tableSize(wanted: Int): Int = {
      var size = 16
      while (size < wanted * 2) { size <<= 1 }
      size
    }

    def size: Int = count

    /** `names[id]` */
    def name(id: Int): String = {
      if (id >= count) { throw new IndexOutOfBoundsException(s"$id >= $count") }
      names(id)
    }

    private def slotOf(key: String, table: Array[String]): Int = {
      val h = key.hashCode
      var slot = (h ^ (h >>> 16)) & (table.length - 1)
      while (table(slot) != null && table(slot) != key) { slot = (slot + 1) & (table.length - 1) }
      slot
    }

    /** `ids.get(name, -1)` */
    def get(key: String): Int = {
      val slot = slotOf(key, keys)
      if (keys(slot) == null) -1 else values(slot)
    }

    /** `ids[name]`（無ければ Python の `KeyError` に相当する例外）。 */
    def apply(key: String): Int = {
      val id = get(key)
      if (id < 0) { throw new NoSuchElementException(key) }
      id
    }

    /** `if nm not in ids: ids[nm] = len(names); names.append(nm)` — returns the id. */
    def intern(key: String): Int = {
      val slot = slotOf(key, keys)
      if (keys(slot) != null) { return values(slot) }
      if ((count + 1) * 2 > keys.length) {
        rehash()
        return intern(key)
      }
      keys(slot) = key
      values(slot) = count
      if (count == names.length) { names = Arrays.copyOf(names, grown(names.length)) }
      names(count) = key
      count += 1
      count - 1
    }

    private def rehash(): Unit = {
      val bigger = new Array[String](keys.length * 2)
      val biggerValues = new Array[Int](bigger.length)
      var i = 0
      while (i < keys.length) {
        val key = keys(i)
        if (key != null) {
          val slot = slotOf(key, bigger)
          bigger(slot) = key
          biggerValues(slot) = values(i)
        }
        i += 1
      }
      keys = bigger
      values = biggerValues
    }
  }

  /** Python の `for line in open(path, 'rb')`：'\n' だけで区切り（'\r' は行に残る）、
    * 各行を Latin-1 で 1 バイト = 1 文字の `String` にして渡す。末尾の '\n' は落とす。
    * ファイル全体をメモリに載せない。
    */
  object ByteLines {
    def foreach(path: Path)(f: String => Unit): Unit = {
      val in = new BufferedInputStream(new FileInputStream(path.toFile), 1 << 20)
      try {
        val chunk = new Array[Byte](1 << 20)
        var line = new Array[Byte](256)
        var length = 0
        var read = in.read(chunk)
        while (read != -1) {
          var i = 0
          while (i < read) {
            val b = chunk(i)
            if (b == '\n') {
              f(new String(line, 0, length, StandardCharsets.ISO_8859_1))
              length = 0
            } else {
              if (length == line.length) { line = Arrays.copyOf(line, line.length * 2) }
              line(length) = b
              length += 1
            }
            i += 1
          }
          read = in.read(chunk)
        }
        if (length > 0) { f(new String(line, 0, length, StandardCharsets.ISO_8859_1)) }
      } finally {
        in.close()
      }
    }
  }
}
