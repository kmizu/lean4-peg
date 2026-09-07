import PalPeg.Words

/-!
# Manacher のアルゴリズム（オフライン最大回文半径）

`List α` 上で、各奇数中心 `c` における最大回文半径 `rad x c` を定義し、
標準的な線形時間アルゴリズム `manacher` がそれを計算することを証明する。
さらに接頭辞回文フラグと、展開ループの比較回数の上界を与える。
-/

namespace PalPeg
namespace Manacher

universe u
variable {α : Type u}

/-! ## 奇数中心の回文半径 -/

/-- 中心 `c`、半径 `r` の（奇数長）回文条件。 -/
def PalAt (x : List α) (c r : ℕ) : Prop :=
  r ≤ c ∧ c + r < x.length ∧ ∀ i ≤ r, x[c - i]? = x[c + i]?

instance instDecidablePalAt [DecidableEq α] (x : List α) (c : ℕ) :
    DecidablePred (PalAt x c) := by
  intro r; unfold PalAt; infer_instance

theorem PalAt.mono {x : List α} {c r s : ℕ} (h : PalAt x c r) (hs : s ≤ r) : PalAt x c s :=
  ⟨le_trans hs h.1, by have := h.2.1; omega, fun i hi => h.2.2 i (le_trans hi hs)⟩

theorem palAt_zero {x : List α} {c : ℕ} (h : c < x.length) : PalAt x c 0 :=
  ⟨Nat.zero_le _, by omega, fun i hi => by
    rw [Nat.le_zero.mp hi]; simp⟩

/-- 中心 `c` における最大回文半径。 -/
def rad [DecidableEq α] (x : List α) (c : ℕ) : ℕ :=
  Nat.findGreatest (PalAt x c) x.length

variable [DecidableEq α]

theorem rad_le_length (x : List α) (c : ℕ) : rad x c ≤ x.length := Nat.findGreatest_le _

theorem le_rad {x : List α} {c r : ℕ} (h : PalAt x c r) : r ≤ rad x c :=
  Nat.le_findGreatest (by have := h.2.1; omega) h

theorem palAt_rad {x : List α} {c : ℕ} (h : c < x.length) : PalAt x c (rad x c) :=
  Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (palAt_zero h)

theorem not_palAt_succ_rad {x : List α} {c : ℕ} : ¬ PalAt x c (rad x c + 1) := fun h => by
  have := le_rad h; omega

theorem rad_eq_zero_of_length_le {x : List α} {c : ℕ} (h : x.length ≤ c) : rad x c = 0 := by
  refine Nat.findGreatest_eq_zero_iff.mpr ?_
  intro m _ _ hm
  have := hm.2.1; omega

theorem rad_le_center {x : List α} {c : ℕ} : rad x c ≤ c := by
  rcases Nat.lt_or_ge c x.length with h | h
  · exact (palAt_rad h).1
  · rw [rad_eq_zero_of_length_le h]; exact Nat.zero_le _

theorem rad_add_lt {x : List α} {c : ℕ} (h : c < x.length) : c + rad x c < x.length :=
  (palAt_rad h).2.1

theorem palAt_iff_le_rad {x : List α} {c r : ℕ} (h : c < x.length) :
    PalAt x c r ↔ r ≤ rad x c :=
  ⟨le_rad, fun hr => (palAt_rad h).mono hr⟩

/-! ## 鏡映補題 -/

omit [DecidableEq α] in
/-- 中心 `c` の回文の内部では、添字 `p` と `2c - p` の文字が一致する。 -/
theorem mirror_getElem? {x : List α} {c Rc p : ℕ} (hc : PalAt x c Rc)
    (h1 : c - Rc ≤ p) (h2 : p ≤ c + Rc) : x[p]? = x[2 * c - p]? := by
  rcases Nat.lt_or_ge p c with h | h
  · have := hc.2.2 (c - p) (by omega)
    rw [show c - (c - p) = p from by omega, show c + (c - p) = 2 * c - p from by omega] at this
    exact this
  · have := hc.2.2 (p - c) (by omega)
    rw [show c + (p - c) = p from by omega, show c - (p - c) = 2 * c - p from by omega] at this
    exact this.symm

/-- **鏡映補題（下界）**：右端 `R = c + rad x c` の既知回文の内側 `c ≤ i ≤ R` では、
鏡像中心 `2c - i` の半径と残り幅 `R - i` の最小値が半径の下界になる。 -/
theorem rad_mirror_ge {x : List α} {c i : ℕ} (hcn : c < x.length)
    (hci : c ≤ i) (hiR : i ≤ c + rad x c) :
    min (rad x (2 * c - i)) (c + rad x c - i) ≤ rad x i := by
  set Rc := rad x c with hRc
  set j := 2 * c - i with hj
  have hc : PalAt x c Rc := palAt_rad hcn
  have hRcc : Rc ≤ c := rad_le_center
  have hRn : c + Rc < x.length := rad_add_lt hcn
  have hjc : j ≤ c := by omega
  have hjn : j < x.length := by omega
  have hj' : PalAt x j (rad x j) := palAt_rad hjn
  have hjle : rad x j ≤ j := rad_le_center
  refine le_rad (c := i) ?_
  refine ⟨by omega, by omega, ?_⟩
  intro k hk
  have hk1 : k ≤ rad x j := le_trans hk (min_le_left _ _)
  have hk2 : k ≤ c + Rc - i := le_trans hk (min_le_right _ _)
  have e1 : x[i + k]? = x[j - k]? := by
    rw [mirror_getElem? hc (by omega) (by omega)]
    exact congrArg _ (by omega)
  have e2 : x[i - k]? = x[j + k]? := by
    rw [mirror_getElem? hc (by omega) (by omega)]
    exact congrArg _ (by omega)
  rw [e1, e2, hj'.2.2 k hk1]

/-- **鏡映補題（等号）**：鏡像半径が残り幅より真に小さいときは半径が一致する。 -/
theorem rad_mirror_eq {x : List α} {c i : ℕ} (hcn : c < x.length)
    (hci : c ≤ i) (hiR : i ≤ c + rad x c) (hlt : rad x (2 * c - i) < c + rad x c - i) :
    rad x i = rad x (2 * c - i) := by
  set Rc := rad x c with hRc
  set j := 2 * c - i with hj
  have hc : PalAt x c Rc := palAt_rad hcn
  have hRcc : Rc ≤ c := rad_le_center
  have hRn : c + Rc < x.length := rad_add_lt hcn
  have hjc : j ≤ c := by omega
  have hjn : j < x.length := by omega
  have hin : i < x.length := by omega
  have hj' : PalAt x j (rad x j) := palAt_rad hjn
  have hge : rad x j ≤ rad x i := by
    have := rad_mirror_ge hcn hci hiR
    rw [← hj, ← hRc] at this
    omega
  refine le_antisymm ?_ hge
  by_contra hcon
  set t := rad x j + 1 with ht
  have hti : PalAt x i t := (palAt_rad hin).mono (by omega)
  have key : x[j - t]? = x[j + t]? := by
    have e1 : x[i + t]? = x[j - t]? := by
      rw [mirror_getElem? hc (by omega) (by omega)]
      exact congrArg _ (by omega)
    have e2 : x[i - t]? = x[j + t]? := by
      rw [mirror_getElem? hc (by omega) (by omega)]
      exact congrArg _ (by omega)
    rw [← e1, ← e2]
    exact (hti.2.2 t le_rfl).symm
  have : PalAt x j t := by
    refine ⟨by omega, by omega, ?_⟩
    intro k hk
    rcases Nat.lt_or_ge k t with h | h
    · exact hj'.2.2 k (by omega)
    · rw [show k = t from by omega]; exact key
  have := le_rad this
  omega

/-! ## 展開ループ（fuel 付き） -/

/-- 半径 `r` から `r+1` へ伸ばせるかの判定（1 回の比較）。 -/
def matchOK (x : List α) (i r : ℕ) : Bool :=
  decide (r + 1 ≤ i) && decide (i + (r + 1) < x.length) &&
    decide (x[i - (r + 1)]? = x[i + (r + 1)]?)

theorem palAt_succ_iff {x : List α} {i r : ℕ} :
    PalAt x i (r + 1) ↔ PalAt x i r ∧ matchOK x i r = true := by
  constructor
  · intro h
    refine ⟨h.mono (Nat.le_succ r), ?_⟩
    have h1 : r + 1 ≤ i := h.1
    have h2 : i + (r + 1) < x.length := h.2.1
    have h3 := h.2.2 (r + 1) le_rfl
    simp [matchOK, h1, h2, h3]
  · rintro ⟨h, hm⟩
    simp only [matchOK, Bool.and_eq_true, decide_eq_true_eq] at hm
    obtain ⟨⟨h1, h2⟩, h3⟩ := hm
    refine ⟨h1, h2, ?_⟩
    intro k hk
    rcases Nat.lt_or_ge k (r + 1) with hlt | hge
    · exact h.2.2 k (by omega)
    · rw [show k = r + 1 from by omega]; exact h3

/-- `r` から始めて一致する限り半径を伸ばす。`fuel` は打ち切り上限。 -/
def expandAux (x : List α) (i : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | fuel + 1, r => if matchOK x i r then expandAux x i fuel (r + 1) else r

theorem expandAux_eq {x : List α} {i : ℕ} :
    ∀ (fuel r : ℕ), PalAt x i r → rad x i - r ≤ fuel → expandAux x i fuel r = rad x i := by
  intro fuel
  induction fuel with
  | zero =>
    intro r h hf
    have := le_rad h
    simp only [expandAux]
    omega
  | succ fuel ih =>
    intro r h hf
    have hin : i < x.length := by have := h.2.1; omega
    rw [expandAux]
    split
    · next hm =>
      have h' : PalAt x i (r + 1) := palAt_succ_iff.mpr ⟨h, hm⟩
      have := le_rad h'
      exact ih (r + 1) h' (by omega)
    · next hm =>
      have hnp : ¬ PalAt x i (r + 1) := by
        intro hp
        exact hm (palAt_succ_iff.mp hp).2
      have hle : rad x i ≤ r := by
        by_contra hcon
        exact hnp ((palAt_rad hin).mono (by omega))
      have := le_rad h
      omega

/-- 半径 `r₀` から始める展開。 -/
def expand (x : List α) (i r₀ : ℕ) : ℕ := expandAux x i x.length r₀

theorem expand_eq {x : List α} {i r₀ : ℕ} (h : PalAt x i r₀) : expand x i r₀ = rad x i :=
  expandAux_eq _ _ h (by have := rad_le_length x i; omega)

/-! ## 走査ループ -/

/-- 走査の状態：既計算半径列 `acc`、最右回文の中心 `c` と右端 `R`、成功比較回数 `w`。 -/
structure State where
  acc : Array ℕ
  c : ℕ
  R : ℕ
  w : ℕ

/-- 添字 `i` における 1 ステップ。 -/
def step (x : List α) (i : ℕ) (s : State) : State :=
  let r₀ := if i < s.R then min (s.acc.getD (2 * s.c - i) 0) (s.R - i) else 0
  let r := expand x i r₀
  { acc := s.acc.push r,
    c := if s.R < i + r then i else s.c,
    R := if s.R < i + r then i + r else s.R,
    w := s.w + (r - r₀) }

/-- 先頭 `n` 個の中心を走査した状態。 -/
def run (x : List α) : ℕ → State
  | 0 => ⟨#[], 0, 0, 0⟩
  | i + 1 => step x i (run x i)

/-- Manacher のアルゴリズム：各中心の最大回文半径の列。 -/
def manacher (x : List α) : List ℕ := (run x x.length).acc.toList

/-- 展開で成功した比較の総数。 -/
def work (x : List α) : ℕ := (run x x.length).w

/-! ## 不変条件と正当性 -/

/-- 走査の不変条件。 -/
def Inv (x : List α) (i : ℕ) (s : State) : Prop :=
  s.acc.size = i ∧
  (∀ j, j < i → s.acc.getD j 0 = rad x j) ∧
  s.R ≤ x.length ∧
  s.w ≤ s.R ∧
  (i < s.R → s.c < i ∧ s.R = s.c + rad x s.c ∧ s.c < x.length)

theorem inv_run {x : List α} : ∀ i, i ≤ x.length → Inv x i (run x i) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨rfl, fun j hj => absurd hj (by omega), ?_, ?_, ?_⟩ <;> simp [run]
  | succ i ih =>
    intro hi
    have hin : i < x.length := by omega
    obtain ⟨hsize, hget, hRn, hwR, hcR⟩ := ih (by omega)
    set s := run x i with hs
    -- 種 r₀ の定義を展開
    obtain ⟨r₀, hr0⟩ : ∃ r₀, r₀ = (if i < s.R then min (s.acc.getD (2 * s.c - i) 0) (s.R - i)
        else 0) := ⟨_, rfl⟩
    have hr0R : i < s.R → r₀ ≤ s.R - i := by
      intro h; rw [hr0, if_pos h]; exact min_le_right _ _
    have hr0z : s.R ≤ i → r₀ = 0 := by
      intro h; rw [hr0, if_neg (by omega)]
    have hpal0 : PalAt x i r₀ := by
      rw [hr0]
      split
      · next hlt =>
        obtain ⟨hci, hRc, hcn⟩ := hcR hlt
        have hj : 2 * s.c - i < i := by omega
        rw [hget _ hj]
        have := rad_mirror_ge (x := x) (c := s.c) (i := i) hcn (by omega) (by omega)
        exact (palAt_rad hin).mono (by omega)
      · exact palAt_zero hin
    have hr : expand x i r₀ = rad x i := expand_eq hpal0
    have hr0le : r₀ ≤ rad x i := le_rad hpal0
    have hradlt : i + rad x i < x.length := rad_add_lt hin
    -- 仕事量の鍵：`r₀ = R - i` か `rad x i = r₀`
    have hkey : i < s.R → r₀ = s.R - i ∨ rad x i = r₀ := by
      intro hlt
      obtain ⟨hci, hRc, hcn⟩ := hcR hlt
      have hj : 2 * s.c - i < i := by omega
      have hr0' : r₀ = min (rad x (2 * s.c - i)) (s.R - i) := by
        rw [hr0, if_pos hlt, hget _ hj]
      rcases Nat.lt_or_ge (rad x (2 * s.c - i)) (s.R - i) with h | h
      · right
        rw [hr0', min_eq_left (le_of_lt h)]
        exact rad_mirror_eq hcn (by omega) (by omega) (by omega)
      · left; rw [hr0', min_eq_right h]
    have hacc : ∀ j, j < i + 1 → (s.acc.push (rad x i)).getD j 0 = rad x j := by
      intro j hj
      rcases Nat.lt_or_ge j i with h | h
      · have hjs : j < s.acc.size := by omega
        rw [show (s.acc.push (rad x i)).getD j 0 = s.acc.getD j 0 from by
          simp [Array.getD, hjs, Nat.lt_succ_of_lt, Array.getElem_push_lt]]
        exact hget j h
      · have hji : j = i := by omega
        have h2 : (s.acc.push (rad x i)).getD j 0 = rad x i := by
          rw [hji, ← hsize]; simp [Array.getD]
        rw [h2, hji]
    show Inv x (i + 1) (step x i s)
    simp only [step, Inv, ← hr0, hr]
    by_cases hb : s.R < i + rad x i
    · simp only [if_pos hb]
      refine ⟨by simp [hsize], hacc, by omega, ?_, fun _ => ⟨by omega, by trivial, hin⟩⟩
      rcases Nat.lt_or_ge i s.R with h | h
      · have := hkey h; have := hr0R h; omega
      · have := hr0z h; omega
    · simp only [if_neg hb]
      refine ⟨by simp [hsize], hacc, hRn, ?_, ?_⟩
      · rcases Nat.lt_or_ge i s.R with h | h
        · have := hkey h; have := hr0R h; omega
        · have := hr0z h; omega
      · intro hlt
        obtain ⟨a, b, c⟩ := hcR (by omega)
        exact ⟨by omega, b, c⟩

/-- **正当性**：`manacher x` の第 `c` 成分は最大回文半径 `rad x c`。 -/
theorem manacher_spec (x : List α) :
    ∀ c, c < x.length → (manacher x)[c]? = some (rad x c) := by
  intro c hc
  obtain ⟨hsize, hget, -⟩ := inv_run x.length le_rfl
  have hcs : c < (run x x.length).acc.size := by omega
  rw [manacher]
  rw [show (run x x.length).acc.toList[c]? = (run x x.length).acc[c]? from by simp,
    Array.getElem?_eq_getElem hcs]
  have := hget c hc
  simp [Array.getD, hcs] at this
  rw [this]

theorem length_manacher (x : List α) : (manacher x).length = x.length := by
  obtain ⟨hsize, -⟩ := inv_run x.length le_rfl
  simp [manacher, hsize]

/-! ## 偶数中心の回文半径 -/

/-- 偶数中心（`c-1` と `c` の間）、半径 `r` の回文条件。 -/
def PalAtE (x : List α) (c r : ℕ) : Prop :=
  r ≤ c ∧ c + r ≤ x.length ∧ ∀ i < r, x[c - 1 - i]? = x[c + i]?

instance instDecidablePalAtE (x : List α) (c : ℕ) :
    DecidablePred (PalAtE x c) := by
  intro r; unfold PalAtE; infer_instance

omit [DecidableEq α] in
theorem PalAtE.mono {x : List α} {c r t : ℕ} (h : PalAtE x c r) (ht : t ≤ r) : PalAtE x c t :=
  ⟨le_trans ht h.1, by have := h.2.1; omega, fun i hi => h.2.2 i (by omega)⟩

omit [DecidableEq α] in
theorem palAtE_zero {x : List α} {c : ℕ} (h : c ≤ x.length) : PalAtE x c 0 :=
  ⟨Nat.zero_le _, by omega, fun i hi => absurd hi (by omega)⟩

/-- 偶数中心 `c` における最大回文半径。 -/
def radE (x : List α) (c : ℕ) : ℕ := Nat.findGreatest (PalAtE x c) x.length

theorem le_radE {x : List α} {c r : ℕ} (h : PalAtE x c r) : r ≤ radE x c :=
  Nat.le_findGreatest (by have := h.2.1; omega) h

theorem palAtE_radE {x : List α} {c : ℕ} (h : c ≤ x.length) : PalAtE x c (radE x c) :=
  Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (palAtE_zero h)

theorem palAtE_iff_le_radE {x : List α} {c r : ℕ} (h : c ≤ x.length) :
    PalAtE x c r ↔ r ≤ radE x c :=
  ⟨le_radE, fun hr => (palAtE_radE h).mono hr⟩

/-! ## 接頭辞回文フラグ -/

omit [DecidableEq α] in
/-- 接頭辞が回文であることの添字による特徴づけ。 -/
theorem isPal_take_iff_index {x : List α} {L : ℕ} (hL : L ≤ x.length) :
    IsPal (x.take L) ↔ ∀ i, i < L → x[i]? = x[L - 1 - i]? := by
  have hlen : (x.take L).length = L := by simp only [List.length_take]; omega
  rw [isPal_iff_getElem?, hlen]
  constructor
  · intro h i hi
    have := h i hi
    rwa [List.getElem?_take_of_lt hi,
      List.getElem?_take_of_lt (show L - 1 - i < L from by omega)] at this
  · intro h i hi
    rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt (show L - 1 - i < L from by omega)]
    exact h i hi

/-- 奇数長の接頭辞が回文 ⟺ 中心 `r` の半径が `r` 以上。 -/
theorem isPal_take_odd_iff {x : List α} {r : ℕ} (hL : 2 * r + 1 ≤ x.length) :
    IsPal (x.take (2 * r + 1)) ↔ r ≤ rad x r := by
  rw [isPal_take_iff_index hL, ← palAt_iff_le_rad (show r < x.length from by omega)]
  constructor
  · intro h
    refine ⟨le_rfl, by omega, ?_⟩
    intro k hk
    have := h (r - k) (by omega)
    rwa [show 2 * r + 1 - 1 - (r - k) = r + k from by omega] at this
  · intro h i hi
    rcases Nat.lt_or_ge r i with hir | hir
    · have := h.2.2 (i - r) (by omega)
      rw [show r - (i - r) = 2 * r + 1 - 1 - i from by omega,
        show r + (i - r) = i from by omega] at this
      exact this.symm
    · have := h.2.2 (r - i) (by omega)
      rwa [show r - (r - i) = i from by omega,
        show r + (r - i) = 2 * r + 1 - 1 - i from by omega] at this

/-- 偶数長の接頭辞が回文 ⟺ 偶数中心 `r` の半径が `r` 以上。 -/
theorem isPal_take_even_iff {x : List α} {r : ℕ} (hL : 2 * r ≤ x.length) :
    IsPal (x.take (2 * r)) ↔ r ≤ radE x r := by
  rw [isPal_take_iff_index hL, ← palAtE_iff_le_radE (show r ≤ x.length from by omega)]
  constructor
  · intro h
    refine ⟨le_rfl, by omega, ?_⟩
    intro k hk
    have := h (r - 1 - k) (by omega)
    rwa [show 2 * r - 1 - (r - 1 - k) = r + k from by omega] at this
  · intro h i hi
    rcases Nat.lt_or_ge i r with hir | hir
    · have := h.2.2 (r - 1 - i) (by omega)
      rwa [show r - 1 - (r - 1 - i) = i from by omega,
        show r + (r - 1 - i) = 2 * r - 1 - i from by omega] at this
    · have := h.2.2 (i - r) (by omega)
      rw [show r - 1 - (i - r) = 2 * r - 1 - i from by omega,
        show r + (i - r) = i from by omega] at this
      exact this.symm

instance instDecidableIsPal (x : List α) : Decidable (IsPal x) :=
  inferInstanceAs (Decidable (x.reverse = x))

/-- 各長さ `L = 0, …, n` について接頭辞 `x.take L` が回文かのフラグ列（参照定義）。 -/
def prefixPalFlags (x : List α) : List Bool :=
  (List.range (x.length + 1)).map (fun L => decide (IsPal (x.take L)))

/-- 半径表から読み出した接頭辞回文フラグ列。 -/
def prefixPalFlagsFromRad (x : List α) : List Bool :=
  (List.range (x.length + 1)).map (fun L =>
    if L % 2 = 1 then decide (L / 2 ≤ rad x (L / 2)) else decide (L / 2 ≤ radE x (L / 2)))

/-- **半径表からの接頭辞回文フラグは参照定義と一致する。** -/
theorem prefixPalFlagsFromRad_eq (x : List α) : prefixPalFlagsFromRad x = prefixPalFlags x := by
  unfold prefixPalFlagsFromRad prefixPalFlags
  refine List.map_congr_left ?_
  intro L hL
  rw [List.mem_range] at hL
  by_cases hp : L % 2 = 1
  · rw [if_pos hp]
    refine decide_eq_decide.mpr ?_
    have hL2 : L = 2 * (L / 2) + 1 := by omega
    rw [show x.take L = x.take (2 * (L / 2) + 1) from by rw [← hL2]]
    exact (isPal_take_odd_iff (by omega)).symm
  · rw [if_neg hp]
    refine decide_eq_decide.mpr ?_
    have hL2 : L = 2 * (L / 2) := by omega
    rw [show x.take L = x.take (2 * (L / 2)) from by rw [← hL2]]
    exact (isPal_take_even_iff (by omega)).symm

/-! ## 仕事量の上界 -/

/-- **仕事量の上界**：展開の成功比較回数は `n` 以下（したがって `2n` 以下）。 -/
theorem work_le_length (x : List α) : work x ≤ x.length := by
  obtain ⟨-, -, hRn, hwR, -⟩ := inv_run x.length le_rfl
  exact le_trans hwR hRn

theorem work_le (x : List α) : work x ≤ 2 * x.length := by
  have := work_le_length x; omega

/-! ## 具体例 -/

section Examples

private def ex : List ℕ := [0, 1, 0, 0, 1, 0]

example : manacher ex = [0, 1, 0, 0, 1, 0] := by decide
example : prefixPalFlags ex = [true, true, false, true, false, false, true] := by decide
example : prefixPalFlagsFromRad ex = prefixPalFlags ex := prefixPalFlagsFromRad_eq ex
example : radE ex 3 = 3 := by decide
example : work ex ≤ 6 := work_le_length ex

end Examples

end Manacher
end PalPeg

