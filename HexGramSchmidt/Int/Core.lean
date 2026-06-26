module

public import HexGramSchmidt.Basic
public import HexMatrix.Bareiss
public import HexMatrix.Determinant

public section

namespace Hex

namespace GramSchmidt

/-- Promote an index into a shorter prefix to the ambient matrix height. -/
@[expose]
def liftFinLE (i : Fin k) (hk : k ≤ n) : Fin n :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Leading principal Gram matrix of the first `k` rows of an integer basis. -/
@[expose]
def leadingGramMatrixInt (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Matrix Int k k :=
  Matrix.ofFn fun i j =>
    Matrix.dot (b.row (liftFinLE i hk)) (b.row (liftFinLE j hk))

/-- The Gram-Schmidt leading Gram matrix is the leading prefix of the full
Gram matrix. This is the shape equation between the public `gramDet` API and
the one-pass `gramDetVec` implementation. -/
theorem leadingGramMatrixInt_eq_leadingPrefix_gram
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    leadingGramMatrixInt b k hk =
      Matrix.leadingPrefix (Matrix.gramMatrix b) k hk := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [leadingGramMatrixInt, Matrix.leadingPrefix, Matrix.gramMatrix, Matrix.dot, Matrix.ofFn,
    liftFinLE]

/-- Leading principal Gram matrix of the first `k` rows of a rational basis. -/
@[expose]
def leadingGramMatrixRat (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Matrix Rat k k :=
  Matrix.ofFn fun i j =>
    Matrix.dot (b.row (liftFinLE i hk)) (b.row (liftFinLE j hk))

/-- Determinant matrix used by the integral `scaledCoeffs` entry formula:
take the leading `j + 1` Gram matrix and replace its last column by the inner
products with row `i`. -/
@[expose]
def scaledCoeffMatrix (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    Matrix Int (j.val + 1) (j.val + 1) :=
  let hk : j.val + 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt)
  Matrix.ofFn fun p q =>
    let p' := liftFinLE p hk
    if q.val = j.val then
      Matrix.dot (b.row p') (b.row i)
    else
      let q' := liftFinLE q hk
      Matrix.dot (b.row p') (b.row q')

end GramSchmidt

namespace GramSchmidt.Int

/-- Integer lattice membership in the row span of `b`. This mirrors the LLL
predicate without making `hex-gram-schmidt` depend on the downstream LLL
library. -/
@[expose]
def memLattice (b : Matrix Int n m) (v : Vector Int m) : Prop :=
  ∃ c : Vector Int n, Matrix.rowCombination b c = v

/-- The `k`-th Gram determinant: the determinant of the `k × k` leading
principal Gram matrix of the integer input. -/
@[expose]
def gramDet (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Nat :=
  (Matrix.bareiss (GramSchmidt.leadingGramMatrixInt b k hk)).toNat

/-- Linear independence of the row prefix determinants used by the
Gram-Schmidt theorem surface, stated over the Mathlib-free executable
`gramDet` data. -/
@[expose]
def independent (b : Matrix Int n m) : Prop :=
  ∀ k : Fin n, 0 < gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt)

/-- Product of the squared Gram-Schmidt basis norms along the first `k` rows. -/
@[expose]
noncomputable def gramSchmidtNormProduct (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    Rat :=
  (List.finRange k).foldl
    (fun acc j =>
      let jn : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
      acc * Vector.normSq ((basis b).row jn))
    1

/-- Read a diagonal entry from a Bareiss elimination matrix as a natural
determinant value. -/
@[expose]
def bareissDiagNat (data : Matrix.BareissData n) (r : Nat) (hr : r < n) : Nat :=
  let i : Fin n := ⟨r, hr⟩
  ((data.matrix.get i).get i).toNat

/-- Read the `k`-th leading-principal determinant from one no-pivot Bareiss
elimination pass over the full Gram matrix. This helper is only used for Gram
matrices: once a leading row prefix is singular, every larger leading prefix is
also singular, so all later leading determinants are zero. -/
@[expose]
def gramDetVecEntry (data : Matrix.BareissData n) (k : Fin (n + 1)) : Nat :=
  match hk : k.val with
  | 0 => 1
  | r + 1 =>
      have hrSucc : r + 1 < n + 1 := by
        simpa [hk] using k.isLt
      have hr : r < n := Nat.succ_lt_succ_iff.mp hrSucc
      match data.singularStep with
      | some s => if s < r + 1 then 0 else
          bareissDiagNat data r hr
      | none => bareissDiagNat data r hr

/-- After a no-pivot Bareiss pass records a singular step, every later
`gramDetVecEntry` slot is the encoded zero tail rather than a diagonal read. -/
private theorem gramDetVecEntry_eq_zero_of_singularStep_lt
    (data : Matrix.BareissData n) (s r : Nat) (hr : r < n)
    (hsing : data.singularStep = some s) (hs : s < r + 1) :
    gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 := by
  simp [gramDetVecEntry, hsing, hs]

/-- Specialization of the encoded zero-tail fact to the no-pivot executable
data used by the Gram determinant vector pass. -/
theorem gramDetVecEntry_noPivot_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (s r : Nat) (hr : r < n)
    (hsing : (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).singularStep = some s)
    (hs : s < r + 1) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 :=
  gramDetVecEntry_eq_zero_of_singularStep_lt
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)) s r hr hsing hs

/-- Mutable loop state for the integer scaled Gram-Schmidt pass: the current
step, the working matrix and coefficient arrays, and the previous Bareiss
pivot. -/
structure ScaledCoeffArrayState where
  step : Nat
  matrix : Array (Array Int)
  coeffs : Array (Array Int)
  prevPivot : Int

/-- Read entry `(row, col)` from a row-major nested array as `rows[row]![col]!`. -/
@[inline] def getArrayEntry (rows : Array (Array Int)) (row col : Nat) : Int :=
  rows[row]![col]!

/-- An `n × n` row-major nested array initialised to all zeros. -/
@[expose]
def zeroRows (n : Nat) : Array (Array Int) :=
  Array.replicate n (Array.replicate n 0)

/-- The Gram matrix of `b` packaged as a row-major nested integer array. -/
@[expose]
def gramRows (b : Matrix Int n m) : Array (Array Int) :=
  Array.ofFn fun i : Fin n =>
    Array.ofFn fun j : Fin n =>
      Matrix.dot (b.row i) (b.row j)

/-- Reading entry `(i, j)` of `gramRows b` recovers the Gram matrix entry
`(gramMatrix b)[i][j]`. -/
private theorem getArrayEntry_gramRows (b : Matrix Int n m) (i j : Fin n) :
    getArrayEntry (gramRows b) i.val j.val = (Matrix.gramMatrix b)[i][j] := by
  simp [getArrayEntry, gramRows, Matrix.gramMatrix, Matrix.dot, Matrix.ofFn]

/-- Reconstruct an `n × n` integer matrix from a row-major nested array, reading
entry `(i, j)` as `rows[i]![j]!` (`getArrayEntry`). This converts the executable
array passes back to the `Matrix` API; for the Gram rows it inverts `gramRows`,
so `rowsToMatrix (gramRows b) n = gramMatrix b`. -/
@[expose]
def rowsToMatrix (rows : Array (Array Int)) (n : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j => getArrayEntry rows i.val j.val

/-- `rowsToMatrix` inverts `gramRows`, recovering `gramMatrix b` from its
nested-array packaging. -/
private theorem rowsToMatrix_gramRows (b : Matrix Int n m) :
    rowsToMatrix (gramRows b) n = Matrix.gramMatrix b := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simpa [rowsToMatrix, Matrix.ofFn] using
    getArrayEntry_gramRows b (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n)

/-- Write `value` into entry `(row, col)` of a row-major nested array. -/
@[expose]
def setArrayEntry (rows : Array (Array Int)) (row col : Nat) (value : Int) :
    Array (Array Int) :=
  rows.set! row (rows[row]!.set! col value)

/-- Reading back the just-written index of `Array.set!` returns the written
value, when the index is in bounds. -/
private theorem array_getElem!_set!_same {α : Type} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.set! i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  simp [Array.getD, Array.set!_eq_setIfInBounds, hi]

/-- Reading a different index after `Array.set!` returns the original element. -/
private theorem array_getElem!_set!_ne {α : Type} [Inhabited α]
    (xs : Array α) {i j : Nat} (hij : j ≠ i) (v : α) :
    (xs.set! i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.set!
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hij.symm]
  · simp [hi]

/-- `setArrayEntry` leaves entries in any other row unchanged. -/
private theorem getArrayEntry_setArrayEntry_of_row_ne
    (rows : Array (Array Int)) (row col r c : Nat) (value : Int) (hr : r ≠ row) :
    getArrayEntry (setArrayEntry rows row col value) r c = getArrayEntry rows r c := by
  grind [getArrayEntry, setArrayEntry]

/-- `setArrayEntry` leaves entries in any other column of the written row
unchanged. -/
private theorem getArrayEntry_setArrayEntry_of_col_ne
    (rows : Array (Array Int)) (row col c : Nat) (value : Int) (hc : c ≠ col) :
    getArrayEntry (setArrayEntry rows row col value) row c = getArrayEntry rows row c := by
  grind [getArrayEntry, setArrayEntry]

/-- Reading back the just-written entry of `setArrayEntry` returns the written
value, when both indices are in bounds. -/
private theorem getArrayEntry_setArrayEntry_self
    (rows : Array (Array Int)) (row col : Nat) (value : Int)
    (hrow : row < rows.size) (hcol : col < rows[row]!.size) :
    getArrayEntry (setArrayEntry rows row col value) row col = value := by
  unfold getArrayEntry setArrayEntry
  rw [array_getElem!_set!_same rows hrow (rows[row]!.set! col value)]
  exact array_getElem!_set!_same rows[row]! hcol value

/-- `setArrayEntry` preserves the outer-array size. -/
private theorem setArrayEntry_size (rows : Array (Array Int)) (row col : Nat) (value : Int) :
    (setArrayEntry rows row col value).size = rows.size := by
  simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- `setArrayEntry` preserves each inner row's size. -/
private theorem setArrayEntry_rows_size
    (rows : Array (Array Int)) (row col r : Nat) (value : Int) :
    (setArrayEntry rows row col value)[r]!.size = rows[r]!.size := by
  unfold setArrayEntry
  by_cases hrow : r = row
  · subst r
    by_cases hbound : row < rows.size
    · rw [array_getElem!_set!_same _ hbound]
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    · simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hbound]
  · simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.set!_eq_setIfInBounds]
    have hne : row ≠ r := fun h => hrow h.symm
    by_cases hbound : row < rows.size
    · simp [hne]
    · simp [Array.setIfInBounds, hbound]

/-- A `foldl` of column-`k` writes over rows all exceeding `k` leaves entries
strictly above the diagonal (`i < j`) unchanged. -/
private theorem getArrayEntry_foldl_setArrayEntry_col_above
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k i j : Nat)
    (hxs : ∀ x ∈ xs, k < x) (hij : i < j) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        i j =
      getArrayEntry coeffs i j := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : k < x := hxs x (by simp)
      have hxs' : ∀ y ∈ xs, k < y := by
        intro y hy
        exact hxs y (by simp [hy])
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hxs']
      by_cases hrow : i = x
      · subst x
        rw [getArrayEntry_setArrayEntry_of_col_ne]
        omega
      · rw [getArrayEntry_setArrayEntry_of_row_ne]
        exact hrow

/-- A `foldl` of column-`k` writes over rows all exceeding `k` leaves entries
in rows at or below `k` unchanged. -/
private theorem getArrayEntry_foldl_setArrayEntry_row_ne
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k i j : Nat)
    (hxs : ∀ x ∈ xs, k < x) (hi : i ≤ k) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        i j =
      getArrayEntry coeffs i j := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : k < x := hxs x (by simp)
      have hxs' : ∀ y ∈ xs, k < y := by
        intro y hy
        exact hxs y (by simp [hy])
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hxs']
      rw [getArrayEntry_setArrayEntry_of_row_ne]
      omega

/-- A column-targeted `foldl` preserves rows whose index is absent from the
write list. -/
private theorem getArrayEntry_foldl_setArrayEntry_row_notMem
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r c : Nat)
    (hr : r ∉ xs) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r c =
      getArrayEntry coeffs r c := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hrx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hrxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hrxs]
      rw [getArrayEntry_setArrayEntry_of_row_ne]
      exact hrx

/-- A column-targeted `foldl` of `setArrayEntry`s at column `k` leaves entries
in any other column unchanged. -/
private theorem getArrayEntry_foldl_setArrayEntry_col_ne
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r c : Nat) (hc : c ≠ k) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r c =
      getArrayEntry coeffs r c := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k))]
      by_cases hrow : r = x
      · subst x
        rw [getArrayEntry_setArrayEntry_of_col_ne _ _ _ _ _ hc]
      · rw [getArrayEntry_setArrayEntry_of_row_ne]
        exact hrow

/-- A column-targeted `foldl` records the source-row value at an updated row.
The row list is nodup, so the final write to `r` is the unique write to that
row. -/
private theorem getArrayEntry_foldl_setArrayEntry_col_mem
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r : Nat)
    (hrmem : r ∈ xs) (hnodup : xs.Nodup)
    (hrow : r < coeffs.size) (hcol : k < coeffs[r]!.size) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r k =
      getArrayEntry rows r k := by
  induction xs generalizing coeffs with
  | nil =>
      exact absurd hrmem (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hrmem with hr_eq | hr_in
      · subst x
        rw [getArrayEntry_foldl_setArrayEntry_row_notMem]
        · exact getArrayEntry_setArrayEntry_self coeffs r k
            (getArrayEntry rows r k) hrow hcol
        · exact hxnotmem
      · have hr_ne_x : r ≠ x := by
          intro h
          subst r
          exact hxnotmem hr_in
        have hrow' : r < (setArrayEntry coeffs x k (getArrayEntry rows x k)).size := by
          simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hrow]
        have hcol' :
            k < (setArrayEntry coeffs x k (getArrayEntry rows x k))[r]!.size := by
          unfold setArrayEntry
          rw [array_getElem!_set!_ne _ hr_ne_x]
          exact hcol
        exact ih (setArrayEntry coeffs x k (getArrayEntry rows x k))
          hr_in hnodup' hrow' hcol'

/-- A `foldl` whose write value reads the same column being written still
leaves non-member indices unchanged. -/
private theorem getElem!_foldl_setSelf_of_notMem
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∉ xs) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr)[r]! = arr[r]! := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      have hx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih _ hxs]
      grind

/-- A `foldl` whose write value reads the same column being written writes the
function of the original value at every member index of a `Nodup` list. -/
private theorem getElem!_foldl_setSelf_of_mem_nodup
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∈ xs) (hnodup : xs.Nodup) (hbound : r < arr.size) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr)[r]! = f r arr[r]! := by
  induction xs generalizing arr with
  | nil => exact absurd hr (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hr with hr_eq | hr_in
      · subst hr_eq
        rw [getElem!_foldl_setSelf_of_notMem _ _ _ _ hxnotmem]
        grind
      · have hr_ne_x : r ≠ x := by
          intro h
          exact hxnotmem (h ▸ hr_in)
        have hbound' : r < (arr.set! x (f x arr[x]!)).size := by
          simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hbound]
        rw [ih _ hr_in hnodup' hbound']
        grind

/-- A `foldl` that sets indices via values read from the row itself preserves
the array size. -/
private theorem size_foldl_setSelf
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- `Array.modify` equals `Array.set!` applied to the function's value at the
current entry. -/
private theorem modify_eq_set!
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α) :
    arr.modify i f = arr.set! i (f arr[i]!) := by
  -- `Array.modify`/`modifyM` are public but not `@[expose]`d, so prove via the
  -- exposed `@[grind]` lemma API rather than unfolding the definitions.
  grind

/-- `Array.modify` leaves any index other than the modified one unchanged. -/
private theorem getElem!_modify_ne
    {α : Type} [Inhabited α] (arr : Array α) (i r : Nat) (f : α → α)
    (hr : r ≠ i) :
    (arr.modify i f)[r]! = arr[r]! := by
  rw [modify_eq_set!]
  grind

/-- Reading back the modified index of `Array.modify` returns `f` applied to the
original entry, when the index is in bounds. -/
private theorem getElem!_modify_self
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α)
    (hi : i < arr.size) :
    (arr.modify i f)[i]! = f arr[i]! := by
  rw [modify_eq_set!]
  grind

/-- `Array.modify` preserves the array size. -/
private theorem modify_size
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α) :
    (arr.modify i f).size = arr.size := by
  rw [modify_eq_set!]
  simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- A `foldl` that modifies indices appearing in `xs` leaves untouched
indices unchanged. -/
private theorem getElem!_foldl_modify_of_notMem
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∉ xs) :
    (xs.foldl (fun next x => next.modify x (f x)) arr)[r]! = arr[r]! := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      have hx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih _ hxs]
      exact getElem!_modify_ne arr x r (f x) hx

/-- A `foldl` that modifies indices appearing in a `Nodup` list `xs` writes
the modified original value at every member index `r` that is in-bounds for the
input array. -/
private theorem getElem!_foldl_modify_of_mem_nodup
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∈ xs) (hnodup : xs.Nodup) (hbound : r < arr.size) :
    (xs.foldl (fun next x => next.modify x (f x)) arr)[r]! = f r arr[r]! := by
  induction xs generalizing arr with
  | nil => exact absurd hr (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hr with hr_eq | hr_in
      · subst hr_eq
        rw [getElem!_foldl_modify_of_notMem _ _ _ _ hxnotmem]
        exact getElem!_modify_self arr r (f r) hbound
      · have hr_ne_x : r ≠ x := by
          intro h
          exact hxnotmem (h ▸ hr_in)
        have hbound' : r < (arr.modify x (f x)).size := by
          rw [modify_size]
          exact hbound
        rw [ih _ hr_in hnodup' hbound']
        rw [getElem!_modify_ne arr x r (f x) hr_ne_x]

/-- A `foldl` that modifies indices via `Array.modify` preserves the outer
array size. -/
private theorem size_foldl_modify
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) :
    (xs.foldl (fun next x => next.modify x (f x)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact modify_size arr x (f x)

/-- Write column `k` of the coefficient array, copying the matrix-column values
from row `k` downward. -/
@[expose]
def writeScaledColumn (coeffs rows : Array (Array Int)) (n k : Nat) :
    Array (Array Int) :=
  Id.run do
    let mut next := setArrayEntry coeffs k k (getArrayEntry rows k k)
    for i in [k + 1:n] do
      next := setArrayEntry next i k (getArrayEntry rows i k)
    return next

/-- `writeScaledColumn` leaves strictly-above-diagonal entries (`i < j`)
unchanged. -/
private theorem getArrayEntry_writeScaledColumn_above
    (coeffs rows : Array (Array Int)) (n k i j : Nat) (hij : i < j) :
    getArrayEntry (writeScaledColumn coeffs rows n k) i j = getArrayEntry coeffs i j := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [getArrayEntry_foldl_setArrayEntry_col_above]
  · by_cases hrow : i = k
    · subst k
      rw [getArrayEntry_setArrayEntry_of_col_ne]
      omega
    · rw [getArrayEntry_setArrayEntry_of_row_ne]
      exact hrow
  · intro x hx
    simp at hx
    omega
  · exact hij

/-- `writeScaledColumn` writes the matrix diagonal entry `(k, k)` into the
coefficient diagonal. -/
private theorem getArrayEntry_writeScaledColumn_diag
    (coeffs rows : Array (Array Int)) (n k : Nat)
    (hrow : k < coeffs.size) (hcol : k < coeffs[k]!.size) :
    getArrayEntry (writeScaledColumn coeffs rows n k) k k =
      getArrayEntry rows k k := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [getArrayEntry_foldl_setArrayEntry_row_ne]
  · rw [getArrayEntry_setArrayEntry_self _ _ _ _ hrow hcol]
  · intro x hx
    simp at hx
    omega
  · omega

/-- Below the current pivot row, `writeScaledColumn` records the current
matrix-column value in the coefficient column. -/
private theorem getArrayEntry_writeScaledColumn_below
    (coeffs rows : Array (Array Int)) (n k i : Nat)
    (hki : k < i) (hi : i < n)
    (hrow : i < coeffs.size) (hcol : k < coeffs[i]!.size) :
    getArrayEntry (writeScaledColumn coeffs rows n k) i k =
      getArrayEntry rows i k := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have hmem : i ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨i - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  have hrow' : i < (setArrayEntry coeffs k k (getArrayEntry rows k k)).size := by
    simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hrow]
  have hcol' :
      k < (setArrayEntry coeffs k k (getArrayEntry rows k k))[i]!.size := by
    unfold setArrayEntry
    rw [array_getElem!_set!_ne _ (show i ≠ k by omega)]
    exact hcol
  exact getArrayEntry_foldl_setArrayEntry_col_mem
    (List.range' (k + 1) (n - (k + 1)))
    (setArrayEntry coeffs k k (getArrayEntry rows k k)) rows k i
    hmem hnodup hrow' hcol'

/-- `writeScaledColumn` only updates entries in column `k`; entries in any
other column are unchanged. -/
private theorem getArrayEntry_writeScaledColumn
    (coeffs rows : Array (Array Int)) (n k r c : Nat) (hc : c ≠ k) :
    getArrayEntry (writeScaledColumn coeffs rows n k) r c =
      getArrayEntry coeffs r c := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [getArrayEntry_foldl_setArrayEntry_col_ne _ _ _ _ _ _ hc]
  by_cases hrow : r = k
  · subst r
    rw [getArrayEntry_setArrayEntry_of_col_ne _ _ _ _ _ hc]
  · rw [getArrayEntry_setArrayEntry_of_row_ne]
    exact hrow

/-- A `foldl` of `setArrayEntry` writes at column `k` preserves the
outer-array size. -/
private theorem foldl_setArrayEntry_size
    (xs : List Nat) (init rows : Array (Array Int)) (k : Nat) :
    (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) init).size =
      init.size := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact setArrayEntry_size _ _ _ _

/-- A `foldl` of `setArrayEntry` writes at column `k` preserves inner row sizes. -/
private theorem foldl_setArrayEntry_rows_size
    (xs : List Nat) (init rows : Array (Array Int)) (k r : Nat) :
    (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) init)[r]!.size =
      init[r]!.size := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact setArrayEntry_rows_size _ _ _ _ _

/-- `writeScaledColumn` preserves the outer-array size. -/
private theorem writeScaledColumn_size
    (coeffs rows : Array (Array Int)) (n k : Nat) :
    (writeScaledColumn coeffs rows n k).size = coeffs.size := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [foldl_setArrayEntry_size]
  exact setArrayEntry_size _ _ _ _

/-- `writeScaledColumn` preserves each inner row's size. -/
private theorem writeScaledColumn_rows_size
    (coeffs rows : Array (Array Int)) (n k r : Nat) :
    (writeScaledColumn coeffs rows n k)[r]!.size = coeffs[r]!.size := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [foldl_setArrayEntry_rows_size]
  exact setArrayEntry_rows_size _ _ _ _ _

/-- Every entry of the default (empty) integer array reads back as `0`. -/
private theorem getArrayEntry_default_row (j : Nat) :
    (default : Array Int)[j]! = 0 := by
  rfl

@[expose]
def stepScaledRows (rows : Array (Array Int)) (n k : Nat)
    (pivot prevPivot : Int) : Array (Array Int) :=
  Id.run do
    let mut next := rows
    let pivotRow := rows[k]!
    for i in [k + 1:n] do
      next := next.modify i fun sourceRow =>
        let entryIK := sourceRow[k]!
        Id.run do
          let mut nextRow := sourceRow.set! k 0
          for j in [k + 1:n] do
            let value :=
              Matrix.exactDiv
                (pivot * nextRow[j]! - entryIK * pivotRow[j]!) prevPivot
            nextRow := nextRow.set! j value
          return nextRow
    return next

section StepScaledRowsBookkeeping

/-- After one `stepScaledRows` sweep, rows whose index lies at or below the
current pivot are untouched by the outer fold. -/
private theorem getArrayEntry_stepScaledRows_of_row_le
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hr : r ≤ k) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      getArrayEntry rows r c := by
  show
      (stepScaledRows rows n k pivot prevPivot)[r]![c]! =
        rows[r]![c]!
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  have hnot : r ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hri⟩ := hmem
    omega
  rw [getElem!_foldl_modify_of_notMem _ _ _ _ hnot]

/-- The new row written at trailing index `r` (with `k < r` and `r < n`) by
`stepScaledRows`, expressed in fold form. This is an intermediate
characterisation; downstream lemmas read individual entries via
`getElem!_foldl_set!_*`. -/
private theorem stepScaledRows_row_at_trailing
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r : Nat) (hk : k < r) (hr : r < n) (hrows : r < rows.size) :
    (stepScaledRows rows n k pivot prevPivot)[r]! =
      (List.range' (k + 1) (n - (k + 1))).foldl
        (fun nextRow j =>
          nextRow.set! j
            (Matrix.exactDiv
              (pivot * nextRow[j]! - rows[r]![k]! * getArrayEntry rows k j)
              prevPivot))
        (rows[r]!.set! k 0) := by
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  have hmem : r ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨r - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  rw [getElem!_foldl_modify_of_mem_nodup _ _ _ _ hmem hnodup hrows]
  simp [getArrayEntry]

/-- The pivot column of `stepScaledRows` is cleared at every trailing row. -/
private theorem getArrayEntry_stepScaledRows_pivot_col
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r : Nat) (hk : k < r) (hr : r < n) (hrows : r < rows.size)
    (hk_row : k < rows[r]!.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r k = 0 := by
  show (stepScaledRows rows n k pivot prevPivot)[r]![k]! = 0
  rw [stepScaledRows_row_at_trailing rows n k pivot prevPivot r hk hr hrows]
  have hnot : k ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hki⟩ := hmem
    omega
  rw [getElem!_foldl_setSelf_of_notMem
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - rows[r]![k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hnot]
  grind

/-- Trailing-column entries of `stepScaledRows` are the fraction-free
Bareiss-style update written by the inner sweep. -/
private theorem getArrayEntry_stepScaledRows_trailing
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hkr : k < r) (hr : r < n) (hkc : k < c) (hc : c < n)
    (hrows : r < rows.size) (hcols : c < rows[r]!.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      Matrix.exactDiv
        (pivot * rows[r]![c]! - rows[r]![k]! * getArrayEntry rows k c)
        prevPivot := by
  show
      (stepScaledRows rows n k pivot prevPivot)[r]![c]! =
        Matrix.exactDiv
          (pivot * rows[r]![c]! - rows[r]![k]! * getArrayEntry rows k c)
          prevPivot
  rw [stepScaledRows_row_at_trailing rows n k pivot prevPivot r hkr hr hrows]
  have hmem : c ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨c - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  have hbound : c < (rows[r]!.set! k 0).size := by
    simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hcols]
  rw [getElem!_foldl_setSelf_of_mem_nodup
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - rows[r]![k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hmem hnodup hbound]
  have hck : c ≠ k := by omega
  grind

/-- Entries strictly left of the pivot column of `stepScaledRows` are
preserved at every trailing row: the inner sweep only writes the trailing
window `[k+1, n)`, and the explicit pivot-column zeroing only touches
column `k`. -/
private theorem getArrayEntry_stepScaledRows_of_col_lt
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hkr : k < r) (hr : r < n) (hc : c < k)
    (hrows : r < rows.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      getArrayEntry rows r c := by
  show
      (stepScaledRows rows n k pivot prevPivot)[r]![c]! = rows[r]![c]!
  rw [stepScaledRows_row_at_trailing rows n k pivot prevPivot r hkr hr hrows]
  have hnot : c ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hci⟩ := hmem
    omega
  rw [getElem!_foldl_setSelf_of_notMem
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - rows[r]![k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hnot]
  have hck : c ≠ k := by omega
  grind

/-- The outer-array length of `stepScaledRows` matches the input. The outer
fold only replaces rows already present in `rows` via `Array.set!`, which
preserves array size. -/
private theorem stepScaledRows_size
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int) :
    (stepScaledRows rows n k pivot prevPivot).size = rows.size := by
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  exact size_foldl_modify _ _ _

/-- If the input row storage has the expected square shape, one
`stepScaledRows` sweep preserves every in-bounds row length. -/
private theorem stepScaledRows_rows_size
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (hsize : rows.size = n)
    (hrowsize : ∀ r, r < n → rows[r]!.size = n) :
    ∀ r, r < n → (stepScaledRows rows n k pivot prevPivot)[r]!.size = n := by
  intro r hr
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  let xs := List.range' (k + 1) (n - (k + 1))
  let f : Nat → Array Int → Array Int := fun i sourceRow =>
    (List.range' (k + 1) (n - (k + 1))).foldl
      (fun nextRow j =>
        nextRow.set! j
          (Matrix.exactDiv
            (pivot * nextRow[j]! - sourceRow[k]! * rows[k]![j]!)
            prevPivot))
      (sourceRow.set! k 0)
  by_cases hmem : r ∈ xs
  · have hnodup : xs.Nodup := by
      dsimp [xs]
      exact List.nodup_range'
    have hbound : r < rows.size := by
      rw [hsize]
      exact hr
    rw [getElem!_foldl_modify_of_mem_nodup xs rows f r hmem hnodup hbound]
    dsimp [f]
    have hinner_size :=
      size_foldl_setSelf
        (List.range' (k + 1) (n - (k + 1)))
        (rows[r]!.set! k 0)
        (fun j nextEntry =>
          Matrix.exactDiv
            (pivot * nextEntry - rows[r]![k]! * getArrayEntry rows k j)
            prevPivot)
    simpa [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
      hrowsize r hr] using hinner_size
  · rw [getElem!_foldl_modify_of_notMem xs rows f r hmem]
    exact hrowsize r hr

/-- Per-entry correspondence between the row-mutating array-storage
`stepScaledRows` update and the matrix-storage `Matrix.stepMatrix` update.
Trailing-block entries use the same `Matrix.exactDiv` expression, the pivot
column clears to zero, and entries outside the update region are preserved on
both sides. -/
private theorem getArrayEntry_stepScaledRows_matches_stepMatrix
    {n : Nat} (rows : Array (Array Int)) (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int)
    (hentry : ∀ a b : Fin n, getArrayEntry rows a.val b.val = M[a][b])
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n)
    (i j : Fin n) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) i.val j.val =
      (Matrix.stepMatrix M k pivot prevPivot)[i][j] := by
  rcases Nat.lt_or_ge k i.val with hki | hki
  · rcases Nat.lt_or_ge k j.val with hkj | hkj
    · -- Trailing-block update: divide the Bareiss numerator by `prevPivot`.
      have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
      have hcols : j.val < rows[i.val]!.size := by
        rw [hrowsize i.val i.isLt]; exact j.isLt
      have hij_eq : getArrayEntry rows i.val j.val = M[i][j] := hentry i j
      have hcol_eq :
          getArrayEntry rows i.val k =
            M[i][(⟨k, Nat.lt_trans hki i.isLt⟩ : Fin n)] := by
        simpa using hentry i ⟨k, Nat.lt_trans hki i.isLt⟩
      have hrow_eq :
          getArrayEntry rows k j.val =
            M[(⟨k, Nat.lt_trans hkj j.isLt⟩ : Fin n)][j] := by
        simpa using hentry ⟨k, Nat.lt_trans hkj j.isLt⟩ j
      rw [getArrayEntry_stepScaledRows_trailing rows n k pivot prevPivot
            i.val j.val hki i.isLt hkj j.isLt hrows hcols]
      rw [Matrix.stepMatrix_update_eq M k pivot prevPivot i j hki hkj]
      change Matrix.exactDiv
          (pivot * getArrayEntry rows i.val j.val -
            getArrayEntry rows i.val k * getArrayEntry rows k j.val) prevPivot =
        Matrix.exactDiv
          (pivot * M[i][j] -
            M[i][(⟨k, Nat.lt_trans hki i.isLt⟩ : Fin n)] *
              M[(⟨k, Nat.lt_trans hkj j.isLt⟩ : Fin n)][j]) prevPivot
      rw [hij_eq, hcol_eq, hrow_eq]
    · -- Pivot column or strictly-left column at a trailing row.
      rcases Nat.lt_or_eq_of_le hkj with hkj_lt | hkj_eq
      · -- Strictly left of pivot column: entries preserved on both sides.
        have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
        rw [getArrayEntry_stepScaledRows_of_col_lt rows n k pivot prevPivot
              i.val j.val hki i.isLt hkj_lt hrows]
        rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot i j
              (fun h => Nat.not_lt_of_ge hkj h.2)
              (fun h => Nat.ne_of_lt hkj_lt h.2)]
        exact hentry i j
      · -- Pivot column itself: both sides clear to zero.
        have hjk : j.val = k := hkj_eq
        have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
        have hk_row : k < rows[i.val]!.size := by
          rw [hrowsize i.val i.isLt]
          exact Nat.lt_of_lt_of_le hki (Nat.le_of_lt i.isLt)
        have hLHS :
            getArrayEntry (stepScaledRows rows n k pivot prevPivot) i.val j.val = 0 := by
          rw [hjk]
          exact getArrayEntry_stepScaledRows_pivot_col rows n k pivot prevPivot
            i.val hki i.isLt hrows hk_row
        have hRHS :
            (Matrix.stepMatrix M k pivot prevPivot)[i][j] = 0 :=
          Matrix.stepMatrix_pivot_col_below M k pivot prevPivot i j hki hjk
        rw [hLHS]
        exact hRHS.symm
  · -- Row preserved: at or above pivot row.
    rw [getArrayEntry_stepScaledRows_of_row_le rows n k pivot prevPivot
          i.val j.val hki]
    rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot i j
          (fun h => Nat.not_lt_of_ge hki h.1)
          (fun h => Nat.not_lt_of_ge hki h.1)]
    exact hentry i j

/-- Matrix-level correspondence: one row-mutating `stepScaledRows` array
update, viewed as a matrix via `rowsToMatrix`, equals the corresponding
`Matrix.stepMatrix` update on the matrix view of the same row storage. -/
private theorem rowsToMatrix_stepScaledRows_eq
    {n : Nat} (rows : Array (Array Int)) (k : Nat) (pivot prevPivot : Int)
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n) :
    rowsToMatrix (stepScaledRows rows n k pivot prevPivot) n =
      Matrix.stepMatrix (rowsToMatrix rows n) k pivot prevPivot := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hentry : ∀ a b : Fin n,
      getArrayEntry rows a.val b.val = (rowsToMatrix rows n)[a][b] := by
    intro a b
    simp [rowsToMatrix, Matrix.ofFn]
  simpa [rowsToMatrix, Matrix.ofFn] using
    getArrayEntry_stepScaledRows_matches_stepMatrix rows (rowsToMatrix rows n)
      k pivot prevPivot hentry hsize hrowsize ⟨i, hi⟩ ⟨j, hj⟩

end StepScaledRowsBookkeeping

@[expose]
def scaledCoeffArrayLoop (n fuel : Nat) (state : ScaledCoeffArrayState) :
    ScaledCoeffArrayState :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if state.step < n then
        let k := state.step
        let coeffs := writeScaledColumn state.coeffs state.matrix n k
        let pivot := getArrayEntry state.matrix k k
        if k + 1 < n then
          if pivot = 0 then
            { state with coeffs := coeffs }
          else
            let next : ScaledCoeffArrayState :=
              { step := state.step + 1
                matrix := stepScaledRows state.matrix n k pivot state.prevPivot
                coeffs := coeffs
                prevPivot := pivot }
            scaledCoeffArrayLoop n fuel next
        else
          { state with step := state.step + 1, coeffs := coeffs }
      else
        state

private theorem getArrayEntry_zeroRows (n i j : Nat) :
    getArrayEntry (zeroRows n) i j = 0 := by
  by_cases hi : i < n
  · by_cases hj : j < n <;> simp [zeroRows, getArrayEntry, hi, hj]
  · simp [zeroRows, getArrayEntry, hi, getArrayEntry_default_row]

/-- Outer-array length of the initial Gram row buffer. -/
private theorem gramRows_size (b : Matrix Int n m) : (gramRows b).size = n := by
  simp [gramRows]

/-- Inner-row length of each row of the initial Gram row buffer. -/
private theorem gramRows_row_size (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    (gramRows b)[r]!.size = n := by
  simp [gramRows, hr]

/-- Outer-array length of the initial coefficient buffer. -/
private theorem zeroRows_size (n : Nat) : (zeroRows n).size = n := by
  simp [zeroRows]

/-- Inner-row length of each row of the initial coefficient buffer. -/
private theorem zeroRows_row_size (n : Nat) (r : Nat) (hr : r < n) :
    (zeroRows n)[r]!.size = n := by
  simp [zeroRows, hr]

private theorem getArrayEntry_scaledCoeffArrayLoop_above
    (n fuel : Nat) (state : ScaledCoeffArrayState)
    (hcoeffs : ∀ i j, i < j → getArrayEntry state.coeffs i j = 0)
    (i j : Nat) (hij : i < j) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state).coeffs i j = 0 := by
  induction fuel generalizing state with
  | zero =>
      exact hcoeffs i j hij
  | succ fuel ih =>
      rw [scaledCoeffArrayLoop]
      by_cases hstep : state.step < n
      · simp only [hstep, ↓reduceIte]
        by_cases hnext : state.step + 1 < n
        · simp only [hnext, ↓reduceIte]
          by_cases hpivot : getArrayEntry state.matrix state.step state.step = 0
          · simp only [hpivot, ↓reduceIte]
            rw [getArrayEntry_writeScaledColumn_above _ _ _ _ _ _ hij]
            exact hcoeffs i j hij
          · simp only [hpivot, ↓reduceIte]
            exact ih
              { step := state.step + 1
                matrix := stepScaledRows state.matrix n state.step
                  (getArrayEntry state.matrix state.step state.step) state.prevPivot
                coeffs := writeScaledColumn state.coeffs state.matrix n state.step
                prevPivot := getArrayEntry state.matrix state.step state.step }
              (by
                intro r c hrc
                rw [getArrayEntry_writeScaledColumn_above _ _ _ _ _ _ hrc]
                exact hcoeffs r c hrc)
        · simp only [hnext, ↓reduceIte]
          rw [getArrayEntry_writeScaledColumn_above _ _ _ _ _ _ hij]
          exact hcoeffs i j hij
      · simp only [hstep, ↓reduceIte]
        exact hcoeffs i j hij

/-- Once a coefficient column lies strictly before the current loop step, later
`scaledCoeffArrayLoop` iterations do not rewrite that column. -/
private theorem getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step
    (n fuel : Nat) (state : ScaledCoeffArrayState) (i j : Nat)
    (hj : j < state.step) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state).coeffs i j =
      getArrayEntry state.coeffs i j := by
  induction fuel generalizing state with
  | zero =>
      rfl
  | succ fuel ih =>
      rw [scaledCoeffArrayLoop]
      by_cases hstep : state.step < n
      · simp only [hstep, ↓reduceIte]
        by_cases hnext : state.step + 1 < n
        · simp only [hnext, ↓reduceIte]
          by_cases hpivot : getArrayEntry state.matrix state.step state.step = 0
          · simp only [hpivot, ↓reduceIte]
            rw [getArrayEntry_writeScaledColumn]
            omega
          · simp only [hpivot, ↓reduceIte]
            rw [ih]
            · rw [getArrayEntry_writeScaledColumn]
              omega
            · show j < state.step + 1
              omega
        · simp only [hnext, ↓reduceIte]
          rw [getArrayEntry_writeScaledColumn]
          omega
      · simp only [hstep, ↓reduceIte]

/-- Run one no-pivot fraction-free Gram elimination and record each scaled
coefficient column immediately before the elimination step zeroes it.

This is the **reference formulation** of the scaled-coefficient matrix, kept
for proofs rather than execution. The live algorithm runs `scaledCoeffRowsSchur`
(the per-row Schur recurrence below); `getArrayEntry_scaledCoeffRowsSchur_eq`
proves the two agree entry-for-entry, and that bridge is what connects
`scaledCoeffRowsSchur` to `gramDet` / `scaledCoeffs`. Do not remove this
formulation as "unused": deleting it breaks the correctness proof of the live
path. -/
@[expose]
def scaledCoeffRows (b : Matrix Int n m) : Array (Array Int) :=
  let state :=
    scaledCoeffArrayLoop n n
      { step := 0
        matrix := gramRows b
        coeffs := zeroRows n
        prevPivot := 1 }
  state.coeffs

@[expose]
def schurSigma (rows : Array (Array Int)) (i j : Nat) : Int :=
  Id.run do
    let mut sigma := getArrayEntry rows i 0 * getArrayEntry rows j 0
    for p in [1:j] do
      sigma :=
        Matrix.exactDiv
          (getArrayEntry rows p p * sigma +
            getArrayEntry rows i p * getArrayEntry rows j p)
          (getArrayEntry rows (p - 1) (p - 1))
    return sigma

@[expose]
def schurScaledCoeffEntry
    (rows gram : Array (Array Int)) (i j : Nat) : Int :=
  if j = 0 then
    getArrayEntry gram i 0
  else
    getArrayEntry rows (j - 1) (j - 1) * getArrayEntry gram i j -
      schurSigma rows i j

/-- Per-row Schur-complement scaled Gram-Schmidt coefficient kernel.

Rows are filled from top to bottom; within row `i`, entries `0..i` are written
left to right.  For `j < i` this writes the scaled coefficient `ν[i][j]`; for
`j = i` the same recurrence writes the diagonal Gram determinant `d_{i+1}`. -/
@[expose]
def scaledCoeffRowsSchur (b : Matrix Int n m) : Array (Array Int) :=
  Id.run do
    let gram := gramRows b
    let mut rows := zeroRows n
    for i in [0:n] do
      for j in [0:i + 1] do
        rows := setArrayEntry rows i j (schurScaledCoeffEntry rows gram i j)
    return rows

private theorem getArrayEntry_schurColumnLoop_upper
    (cols : List Nat) (rows gram : Array (Array Int)) (row i j : Nat)
    (hij : i < j) (hcols : ∀ c ∈ cols, c ≤ row) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        i j =
      getArrayEntry rows i j := by
  induction cols generalizing rows with
  | nil =>
      simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      have hcols_tail : ∀ c ∈ cols, c ≤ row := by
        intro c hc
        exact hcols c (List.mem_cons_of_mem col hc)
      rw [ih _ hcols_tail]
      by_cases hrow : i = row
      · subst row
        have hcol_le : col ≤ i := hcols col (by simp)
        rw [getArrayEntry_setArrayEntry_of_col_ne]
        omega
      · rw [getArrayEntry_setArrayEntry_of_row_ne]
        exact hrow

private theorem getArrayEntry_schurRowLoop_upper
    (rowList : List Nat) (rows gram : Array (Array Int)) (i j : Nat)
    (hij : i < j) :
    getArrayEntry
        (rowList.foldl
          (fun next row =>
            (List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              next) rows)
        i j =
      getArrayEntry rows i j := by
  induction rowList generalizing rows with
  | nil =>
      simp
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      rw [ih _]
      rw [getArrayEntry_schurColumnLoop_upper]
      · exact hij
      · intro c hc
        rw [List.mem_range'] at hc
        omega

private theorem getArrayEntry_scaledCoeffRowsSchur_upper
    (b : Matrix Int n m) (i j : Nat) (hij : i < j) :
    getArrayEntry (scaledCoeffRowsSchur b) i j = 0 := by
  simp [scaledCoeffRowsSchur]
  rw [getArrayEntry_schurRowLoop_upper]
  · exact getArrayEntry_zeroRows n i j
  · exact hij

/-- The Schur column loop fixes the active row `row`: cells in any other row
are untouched, irrespective of which columns the loop visits. -/
private theorem getArrayEntry_schurColumnLoop_row_ne
    (cols : List Nat) (rows gram : Array (Array Int)) (row r c : Nat)
    (hr : r ≠ row) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        r c =
      getArrayEntry rows r c := by
  induction cols generalizing rows with
  | nil => simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact getArrayEntry_setArrayEntry_of_row_ne rows row col r c _ hr

/-- Row-completion frame lemma. The outer Schur row loop only writes to rows
listed in `rowList`; cells in rows not in `rowList` retain their initial
values. In particular, once row `i` has been processed by the row loop, the
remaining row iterations preserve every cell `(i, ·)`. -/
private theorem getArrayEntry_schurRowLoop_row_not_mem
    (rowList : List Nat) (rows gram : Array (Array Int)) (i j : Nat)
    (hi : i ∉ rowList) :
    getArrayEntry
        (rowList.foldl
          (fun next row =>
            (List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              next) rows)
        i j =
      getArrayEntry rows i j := by
  induction rowList generalizing rows with
  | nil => simp
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      have hi_ne : i ≠ row := fun h => hi (h ▸ List.mem_cons_self)
      have hi_tail : i ∉ rowList := fun h => hi (List.mem_cons_of_mem row h)
      rw [ih _ hi_tail]
      exact getArrayEntry_schurColumnLoop_row_ne _ rows gram row i j hi_ne

/-- Column-loop stability for the `(row, 0)` cell when the loop never visits
column `0`. Subsequent column writes at a different column keep the cell
unchanged. -/
private theorem getArrayEntry_schurColumnLoop_col_zero_preserve
    (cols : List Nat) (rows gram : Array (Array Int)) (row : Nat)
    (hzero : 0 ∉ cols) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        row 0 =
      getArrayEntry rows row 0 := by
  induction cols generalizing rows with
  | nil => simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      have h_col_ne : col ≠ 0 := fun h => hzero (h ▸ List.mem_cons_self)
      have h_tail : 0 ∉ cols := fun h => hzero (List.mem_cons_of_mem col h)
      rw [ih _ h_tail]
      exact getArrayEntry_setArrayEntry_of_col_ne rows row col 0 _ h_col_ne.symm

/-- Column-loop stability for a cell `(row, col_target)` when the loop never
visits `col_target`. Subsequent column writes at different columns keep
the cell unchanged. -/
private theorem getArrayEntry_schurColumnLoop_col_not_mem
    (cols : List Nat) (rows gram : Array (Array Int)) (row col_target : Nat)
    (h_not_mem : col_target ∉ cols) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        row col_target =
      getArrayEntry rows row col_target := by
  induction cols generalizing rows with
  | nil => simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      have h_col_ne : col ≠ col_target :=
        fun h => h_not_mem (h ▸ List.mem_cons_self)
      have h_tail : col_target ∉ cols :=
        fun h => h_not_mem (List.mem_cons_of_mem col h)
      rw [ih _ h_tail]
      exact getArrayEntry_setArrayEntry_of_col_ne rows row col col_target _
        (fun h => h_col_ne h.symm)

/-- Single-row column-loop dispatch for column `0`. When `0` appears in
`cols`, the column loop ultimately writes `getArrayEntry gram row 0` into the
`(row, 0)` slot. Because the `j = 0` branch of `schurScaledCoeffEntry`
returns the gram entry directly, this value is independent of which other
columns are written before or after. -/
private theorem getArrayEntry_schurColumnLoop_col_zero
    (cols : List Nat) (rows gram : Array (Array Int)) (row : Nat)
    (hzero : 0 ∈ cols)
    (hrow : row < rows.size) (hcol : 0 < rows[row]!.size) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        row 0 =
      getArrayEntry gram row 0 := by
  induction cols generalizing rows with
  | nil => exact absurd hzero (List.not_mem_nil)
  | cons col cols ih =>
      simp only [List.foldl_cons]
      by_cases h_zero_in_tail : 0 ∈ cols
      · have hrow' :
            row < (setArrayEntry rows row col
                (schurScaledCoeffEntry rows gram row col)).size := by
          rw [setArrayEntry_size]; exact hrow
        have hcol' :
            0 < (setArrayEntry rows row col
                (schurScaledCoeffEntry rows gram row col))[row]!.size := by
          rw [setArrayEntry_rows_size]; exact hcol
        exact ih _ h_zero_in_tail hrow' hcol'
      · have h_col_eq : col = 0 := by
          rcases List.mem_cons.mp hzero with h | h
          · exact h.symm
          · exact (h_zero_in_tail h).elim
        subst h_col_eq
        rw [getArrayEntry_schurColumnLoop_col_zero_preserve _ _ _ _ h_zero_in_tail]
        rw [getArrayEntry_setArrayEntry_self _ _ _ _ hrow hcol]
        simp [schurScaledCoeffEntry]

/-- Size preservation: the Schur column loop keeps the outer-array length. -/
private theorem schurColumnLoop_size
    (cols : List Nat) (rows gram : Array (Array Int)) (row : Nat) :
    (cols.foldl
        (fun next col =>
          setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows).size =
      rows.size := by
  induction cols generalizing rows with
  | nil => rfl
  | cons col cols ih => simp only [List.foldl_cons]; rw [ih]; exact setArrayEntry_size _ _ _ _

/-- Size preservation: the Schur column loop keeps each inner row's length. -/
private theorem schurColumnLoop_rows_size
    (cols : List Nat) (rows gram : Array (Array Int)) (row r : Nat) :
    (cols.foldl
        (fun next col =>
          setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)[r]!.size =
      rows[r]!.size := by
  induction cols generalizing rows with
  | nil => rfl
  | cons col cols ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact setArrayEntry_rows_size _ _ _ _ _

/-- Size preservation: the Schur row loop keeps the outer-array length. -/
private theorem schurRowLoop_size
    (rowList : List Nat) (rows gram : Array (Array Int)) :
    (rowList.foldl
      (fun next row =>
        (List.range' 0 (row + 1)).foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
          next) rows).size =
      rows.size := by
  induction rowList generalizing rows with
  | nil => rfl
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact schurColumnLoop_size _ _ _ _

/-- Size preservation: the Schur row loop keeps each inner row's length. -/
private theorem schurRowLoop_rows_size
    (rowList : List Nat) (rows gram : Array (Array Int)) (r : Nat) :
    (rowList.foldl
      (fun next row =>
        (List.range' 0 (row + 1)).foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
          next) rows)[r]!.size =
      rows[r]!.size := by
  induction rowList generalizing rows with
  | nil => rfl
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact schurColumnLoop_rows_size _ _ _ _ _

/-- Outer-array length of the per-row Schur kernel: the row buffer is
allocated as `zeroRows n` and the row loop writes via `setArrayEntry`,
which preserves outer-array size. -/
private theorem scaledCoeffRowsSchur_size (b : Matrix Int n m) :
    (scaledCoeffRowsSchur b).size = n := by
  simp [scaledCoeffRowsSchur]
  rw [schurRowLoop_size]
  exact zeroRows_size n

/-- Row-loop dispatch for the `(i, 0)` boundary. If `i ∈ rowList` and the
initial row buffer is large enough at row `i`, the Schur row loop writes the
`(i, 0)` cell to `getArrayEntry gram i 0` (via the inner column loop) and
leaves it untouched in subsequent row iterations. -/
private theorem getArrayEntry_schurRowLoop_col_zero
    (rowList : List Nat) (rows gram : Array (Array Int)) (i : Nat)
    (hi : i ∈ rowList) (hrow : i < rows.size) (hcol : 0 < rows[i]!.size) :
    getArrayEntry
        (rowList.foldl
          (fun next row =>
            (List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              next) rows)
        i 0 =
      getArrayEntry gram i 0 := by
  induction rowList generalizing rows with
  | nil => exact absurd hi List.not_mem_nil
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      by_cases h_i_in_tail : i ∈ rowList
      · -- Recurse into the tail, deriving size hypotheses via the column-loop
        -- size-preservation lemmas.
        have h_size :
            i < ((List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              rows).size := by
          rw [schurColumnLoop_size]; exact hrow
        have h_row_size :
            0 < ((List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              rows)[i]!.size := by
          rw [schurColumnLoop_rows_size]; exact hcol
        exact ih _ h_i_in_tail h_size h_row_size
      · -- i is exactly the current `row`. The column loop visits `0`
        -- (`List.range' 0 (row + 1)` contains `0`), writes the gram entry
        -- there, and tail row iterations preserve `(i, 0)`.
        have h_i_eq : i = row := by
          rcases List.mem_cons.mp hi with h | h
          · exact h
          · exact (h_i_in_tail h).elim
        subst h_i_eq
        rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ h_i_in_tail]
        apply getArrayEntry_schurColumnLoop_col_zero _ _ _ _ _ hrow hcol
        rw [List.mem_range']
        exact ⟨0, Nat.succ_pos _, by simp⟩

/-- σ-chain dependency frame lemma. The value of `schurSigma rows i j`
depends only on the diagonal cells `rows[k][k]` for `k < j`, the
row-`i` cells `rows[i][p]` for `p < j`, and the row-`j` cells `rows[j][p]`
for `p < j`. The hypothesis `0 < j` makes both initial reads `rows[i][0]`
and `rows[j][0]` fall under `h_i` and `h_j` at `p = 0`. -/
private theorem schurSigma_congr
    {rows rows' : Array (Array Int)} {i j : Nat} (hj : 0 < j)
    (h_diag : ∀ k, k < j → getArrayEntry rows k k = getArrayEntry rows' k k)
    (h_i : ∀ p, p < j → getArrayEntry rows i p = getArrayEntry rows' i p)
    (h_j : ∀ p, p < j → getArrayEntry rows j p = getArrayEntry rows' j p) :
    schurSigma rows i j = schurSigma rows' i j := by
  -- Generic foldl congruence under pointwise body equality.
  have foldl_congr :
      ∀ (L : List Nat) (init init' : Int),
        init = init' →
        (∀ p ∈ L, ∀ s : Int,
          Matrix.exactDiv
            (getArrayEntry rows p p * s +
              getArrayEntry rows i p * getArrayEntry rows j p)
            (getArrayEntry rows (p - 1) (p - 1)) =
          Matrix.exactDiv
            (getArrayEntry rows' p p * s +
              getArrayEntry rows' i p * getArrayEntry rows' j p)
            (getArrayEntry rows' (p - 1) (p - 1))) →
        L.foldl
            (fun sigma p =>
              Matrix.exactDiv
                (getArrayEntry rows p p * sigma +
                  getArrayEntry rows i p * getArrayEntry rows j p)
                (getArrayEntry rows (p - 1) (p - 1)))
            init =
          L.foldl
            (fun sigma p =>
              Matrix.exactDiv
                (getArrayEntry rows' p p * sigma +
                  getArrayEntry rows' i p * getArrayEntry rows' j p)
                (getArrayEntry rows' (p - 1) (p - 1)))
            init' := by
    intro L
    induction L with
    | nil => intro init init' hinit _; simpa using hinit
    | cons p L ih =>
        intro init init' hinit hstep
        simp only [List.foldl_cons]
        apply ih
        · rw [hinit, hstep p (List.mem_cons_self) init']
        · intro q hq s
          exact hstep q (List.mem_cons_of_mem _ hq) s
  -- Initial accumulator equality at `p = 0`.
  have h_init : getArrayEntry rows i 0 * getArrayEntry rows j 0 =
      getArrayEntry rows' i 0 * getArrayEntry rows' j 0 := by
    rw [h_i 0 hj, h_j 0 hj]
  -- Per-step equality, using `p < j` for every `p` in `[1, j)`.
  have h_step :
      ∀ p ∈ List.range' 1 (j - 1), ∀ s : Int,
        Matrix.exactDiv
          (getArrayEntry rows p p * s +
            getArrayEntry rows i p * getArrayEntry rows j p)
          (getArrayEntry rows (p - 1) (p - 1)) =
        Matrix.exactDiv
          (getArrayEntry rows' p p * s +
            getArrayEntry rows' i p * getArrayEntry rows' j p)
          (getArrayEntry rows' (p - 1) (p - 1)) := by
    intro p hp s
    rw [List.mem_range'] at hp
    have hp_lt : p < j := by omega
    have hp_pred_lt : p - 1 < j := by omega
    rw [h_diag p hp_lt, h_i p hp_lt, h_j p hp_lt, h_diag (p - 1) hp_pred_lt]
  -- Reduce `schurSigma` to a foldl on each side.
  show
    (Id.run do
      let mut sigma := getArrayEntry rows i 0 * getArrayEntry rows j 0
      for p in [1:j] do
        sigma :=
          Matrix.exactDiv
            (getArrayEntry rows p p * sigma +
              getArrayEntry rows i p * getArrayEntry rows j p)
            (getArrayEntry rows (p - 1) (p - 1))
      return sigma) =
    (Id.run do
      let mut sigma := getArrayEntry rows' i 0 * getArrayEntry rows' j 0
      for p in [1:j] do
        sigma :=
          Matrix.exactDiv
            (getArrayEntry rows' p p * sigma +
              getArrayEntry rows' i p * getArrayEntry rows' j p)
            (getArrayEntry rows' (p - 1) (p - 1))
      return sigma)
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  exact foldl_congr _ _ _ h_init h_step

/-- `j = 0` boundary frame lemma. After the full Schur kernel runs, the
`(i, 0)` cell holds the gram entry `gram[i][0]`. This is used by the σ-chain
recurrence (`σ₀ = rows[i][0] · rows[j][0]`) when filling in cells at column
`j > 0`. -/
private theorem getArrayEntry_scaledCoeffRowsSchur_col_zero
    (b : Matrix Int n m) (i : Nat) :
    getArrayEntry (scaledCoeffRowsSchur b) i 0 =
      getArrayEntry (gramRows b) i 0 := by
  by_cases hin : i < n
  · -- In bounds. The outer row loop hits row `i`, the inner column loop
    -- writes `gram[i][0]` at `(i, 0)`, and later row iterations leave it
    -- alone.
    have h_mem : i ∈ List.range' 0 n := by
      rw [List.mem_range']
      exact ⟨i, by simpa using hin, by simp⟩
    have h_row : i < (zeroRows n).size := by
      rw [zeroRows_size]; exact hin
    have h_col : 0 < (zeroRows n)[i]!.size := by
      rw [zeroRows_row_size n i hin]
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) hin
    simp [scaledCoeffRowsSchur]
    exact getArrayEntry_schurRowLoop_col_zero (List.range' 0 n) (zeroRows n)
      (gramRows b) i h_mem h_row h_col
  · -- Out of bounds. The row loop never visits row `i`, so `(i, 0)` stays at
    -- its zero initial value, which matches `gramRows b` out of bounds.
    have hin' : n ≤ i := Nat.le_of_not_lt hin
    have h_not_mem : i ∉ List.range' 0 n := by
      rw [List.mem_range']
      rintro ⟨k, hk, hki⟩
      simp at hki
      omega
    have h_gram_zero : getArrayEntry (gramRows b) i 0 = 0 := by
      have h_gram_size : (gramRows b).size = n := gramRows_size b
      have h_size_le : (gramRows b).size ≤ i := h_gram_size.symm ▸ hin'
      have h_entry_default : (gramRows b)[i]! = (default : Array Int) := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none h_size_le, Option.getD_none]
      unfold getArrayEntry
      rw [h_entry_default]
      exact getArrayEntry_default_row 0
    rw [h_gram_zero]
    simp [scaledCoeffRowsSchur]
    rw [getArrayEntry_schurRowLoop_row_not_mem (List.range' 0 n) (zeroRows n)
      (gramRows b) i 0 h_not_mem]
    exact getArrayEntry_zeroRows n i 0

private theorem getArrayEntry_scaledCoeffRowsSchur_eq_schurScaledCoeffEntry
    {n m : Nat} (b : Matrix Int n m) (a c : Nat)
    (h_c_le_a : c ≤ a) (han : a < n) :
    getArrayEntry (scaledCoeffRowsSchur b) a c =
      schurScaledCoeffEntry (scaledCoeffRowsSchur b) (gramRows b) a c := by
  let gram := gramRows b
  let rowPrefix := List.range' 0 a
  let rowSuffix := List.range' (a + 1) (n - (a + 1))
  let rowsBeforeA :=
    rowPrefix.foldl
      (fun next row =>
        (List.range' 0 (row + 1)).foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
          next) (zeroRows n)
  let colPrefix := List.range' 0 c
  let colSuffix := List.range' (c + 1) (a - c)
  let rowsBeforeC :=
    colPrefix.foldl
      (fun next col =>
        setArrayEntry next a col (schurScaledCoeffEntry next gram a col)) rowsBeforeA
  let rowsAfterC :=
    setArrayEntry rowsBeforeC a c (schurScaledCoeffEntry rowsBeforeC gram a c)
  have h_rows_split :
      List.range' 0 n = rowPrefix ++ a :: rowSuffix := by
    dsimp [rowPrefix, rowSuffix]
    have hn_split : n = a + (n - a) := by omega
    have hn_tail : n - a = (n - (a + 1)) + 1 := by omega
    calc
      List.range' 0 n = List.range' 0 (a + (n - a)) := by
        exact congrArg (List.range' 0) hn_split
      _ = List.range' 0 a ++ List.range' a (n - a) := by
        simpa using (List.range'_append_1 (s := 0) (m := a) (n := n - a)).symm
      _ = List.range' 0 a ++ List.range' a ((n - (a + 1)) + 1) := by
        rw [hn_tail]
      _ = List.range' 0 a ++ a :: List.range' (a + 1) (n - (a + 1)) := by
        rw [List.range'_succ]
  have h_cols_split :
      List.range' 0 (a + 1) = colPrefix ++ c :: colSuffix := by
    dsimp [colPrefix, colSuffix]
    have hc_split : a + 1 = c + ((a + 1) - c) := by omega
    have hc_tail : (a + 1) - c = (a - c) + 1 := by omega
    calc
      List.range' 0 (a + 1) = List.range' 0 (c + ((a + 1) - c)) := by
        exact congrArg (List.range' 0) hc_split
      _ = List.range' 0 c ++ List.range' c ((a + 1) - c) := by
        simpa using (List.range'_append_1 (s := 0) (m := c) (n := (a + 1) - c)).symm
      _ = List.range' 0 c ++ List.range' c ((a - c) + 1) := by
        rw [hc_tail]
      _ = List.range' 0 c ++ c :: List.range' (c + 1) (a - c) := by
        rw [List.range'_succ]
  have h_a_not_suffix : a ∉ rowSuffix := by
    dsimp [rowSuffix]
    intro hmem
    rw [List.mem_range'] at hmem
    omega
  have h_c_not_colSuffix : c ∉ colSuffix := by
    dsimp [colSuffix]
    intro hmem
    rw [List.mem_range'] at hmem
    omega
  have hrow_beforeC : a < rowsBeforeC.size := by
    dsimp [rowsBeforeC, rowsBeforeA]
    rw [schurColumnLoop_size, schurRowLoop_size, zeroRows_size]
    exact han
  have hcol_beforeC : c < rowsBeforeC[a]!.size := by
    dsimp [rowsBeforeC, rowsBeforeA]
    rw [schurColumnLoop_rows_size, schurRowLoop_rows_size, zeroRows_row_size n a han]
    exact Nat.lt_of_le_of_lt h_c_le_a han
  have h_write :
      getArrayEntry (scaledCoeffRowsSchur b) a c =
        schurScaledCoeffEntry rowsBeforeC gram a c := by
    simp [scaledCoeffRowsSchur, gram, h_rows_split, h_cols_split, rowsBeforeA,
      rowsBeforeC]
    rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ h_a_not_suffix]
    rw [getArrayEntry_schurColumnLoop_col_not_mem _ _ _ _ _ h_c_not_colSuffix]
    exact getArrayEntry_setArrayEntry_self rowsBeforeC a c
      (schurScaledCoeffEntry rowsBeforeC gram a c) hrow_beforeC hcol_beforeC
  rw [h_write]
  by_cases hc0 : c = 0
  · simp [schurScaledCoeffEntry, hc0, gram]
  · have hcp : 0 < c := Nat.pos_of_ne_zero hc0
    have h_entry_congr :
        schurScaledCoeffEntry rowsBeforeC gram a c =
          schurScaledCoeffEntry (scaledCoeffRowsSchur b) gram a c := by
      simp [schurScaledCoeffEntry, hc0]
      have h_diag_cells :
          ∀ k, k < c →
            getArrayEntry rowsBeforeC k k =
              getArrayEntry (scaledCoeffRowsSchur b) k k := by
        intro k hk
        have hka : k < a := by omega
        have hk_not_a : k ≠ a := by omega
        have hk_not_suffix : k ∉ rowSuffix := by
          dsimp [rowSuffix]
          intro hmem
          rw [List.mem_range'] at hmem
          omega
        calc
          getArrayEntry rowsBeforeC k k =
              getArrayEntry rowsBeforeA k k := by
            dsimp [rowsBeforeC]
            exact getArrayEntry_schurColumnLoop_row_ne _ _ _ _ _ _ hk_not_a
          _ = getArrayEntry
              ((List.range' 0 n).foldl
                (fun next row =>
                  (List.range' 0 (row + 1)).foldl
                    (fun next col =>
                      setArrayEntry next row col
                        (schurScaledCoeffEntry next (gramRows b) row col))
                    next) (zeroRows n)) k k := by
            rw [h_rows_split]
            simp [rowsBeforeA, gram]
            rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ hk_not_suffix]
            rw [getArrayEntry_schurColumnLoop_row_ne _ _ _ _ _ _ hk_not_a]
          _ = getArrayEntry (scaledCoeffRowsSchur b) k k := by
            simp [scaledCoeffRowsSchur]
      have h_row_a_cells :
          ∀ p, p < c →
            getArrayEntry rowsBeforeC a p =
              getArrayEntry (scaledCoeffRowsSchur b) a p := by
        intro p hp
        have hp_not_c : p ∉ colSuffix := by
          dsimp [colSuffix]
          intro hmem
          rw [List.mem_range'] at hmem
          omega
        calc
          getArrayEntry rowsBeforeC a p =
              getArrayEntry rowsAfterC a p := by
            dsimp [rowsAfterC]
            rw [getArrayEntry_setArrayEntry_of_col_ne]
            omega
          _ = getArrayEntry
              ((colPrefix ++ c :: colSuffix).foldl
                (fun next col =>
                  setArrayEntry next a col (schurScaledCoeffEntry next gram a col))
                rowsBeforeA) a p := by
            simp [colPrefix, rowsBeforeC, rowsAfterC]
            rw [getArrayEntry_schurColumnLoop_col_not_mem _ _ _ _ _ hp_not_c]
          _ = getArrayEntry (scaledCoeffRowsSchur b) a p := by
            simp [scaledCoeffRowsSchur, gram, h_rows_split, h_cols_split, rowsBeforeA]
            rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ h_a_not_suffix]
      have h_row_c_cells :
          ∀ p, p < c →
            getArrayEntry rowsBeforeC c p =
              getArrayEntry (scaledCoeffRowsSchur b) c p := by
        intro p hp
        by_cases hca : c = a
        · subst a
          have hp_not_c : p ∉ colSuffix := by
            dsimp [colSuffix]
            intro hmem
            rw [List.mem_range'] at hmem
            omega
          calc
            getArrayEntry rowsBeforeC c p =
                getArrayEntry rowsAfterC c p := by
              dsimp [rowsAfterC]
              rw [getArrayEntry_setArrayEntry_of_col_ne]
              omega
            _ = getArrayEntry
                ((colPrefix ++ c :: colSuffix).foldl
                  (fun next col =>
                    setArrayEntry next c col (schurScaledCoeffEntry next gram c col))
                  rowsBeforeA) c p := by
              simp [colPrefix, rowsBeforeC, rowsAfterC]
              rw [getArrayEntry_schurColumnLoop_col_not_mem _ _ _ _ _ hp_not_c]
            _ = getArrayEntry (scaledCoeffRowsSchur b) c p := by
              simp [scaledCoeffRowsSchur, gram, h_rows_split, h_cols_split, rowsBeforeA]
              rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ h_a_not_suffix]
        · have hca_lt : c < a := by omega
          have hca_ne : c ≠ a := by omega
          have hc_not_suffix : c ∉ rowSuffix := by
            dsimp [rowSuffix]
            intro hmem
            rw [List.mem_range'] at hmem
            omega
          calc
            getArrayEntry rowsBeforeC c p =
                getArrayEntry rowsBeforeA c p := by
              dsimp [rowsBeforeC]
              exact getArrayEntry_schurColumnLoop_row_ne _ _ _ _ _ _ hca_ne
            _ = getArrayEntry
                ((List.range' 0 n).foldl
                  (fun next row =>
                    (List.range' 0 (row + 1)).foldl
                      (fun next col =>
                        setArrayEntry next row col
                          (schurScaledCoeffEntry next (gramRows b) row col))
                      next) (zeroRows n)) c p := by
              rw [h_rows_split]
              simp [rowsBeforeA, gram]
              rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ hc_not_suffix]
              rw [getArrayEntry_schurColumnLoop_row_ne _ _ _ _ _ _ hca_ne]
            _ = getArrayEntry (scaledCoeffRowsSchur b) c p := by
              simp [scaledCoeffRowsSchur]
      have h_diag_prev :
          getArrayEntry rowsBeforeC (c - 1) (c - 1) =
            getArrayEntry (scaledCoeffRowsSchur b) (c - 1) (c - 1) := by
        exact h_diag_cells (c - 1) (by omega)
      have h_sigma :
          schurSigma rowsBeforeC a c =
            schurSigma (scaledCoeffRowsSchur b) a c :=
        schurSigma_congr hcp h_diag_cells h_row_a_cells h_row_c_cells
      rw [h_diag_prev, h_sigma]
    exact h_entry_congr

/-- Integral scaled Gram-Schmidt coefficients. For `j < i`, the entry is the
determinant formula corresponding to `d_{j+1} * μ_{i,j}`; on the diagonal we
store `d_{j+1}`, and entries above the diagonal are zero. -/
structure Data (n : Nat) where
  d : Vector Nat (n + 1)
  ν : Matrix Int n n

@[expose]
def gramDetVecFromScaledCoeffRows (rows : Array (Array Int)) :
    Vector Nat (n + 1) :=
  Vector.ofFn fun k =>
    match hk : k.val with
    | 0 => 1
    | r + 1 =>
        have hrSucc : r + 1 < n + 1 := by
          simpa [hk] using k.isLt
        have _hr : r < n := Nat.succ_lt_succ_iff.mp hrSucc
        (getArrayEntry rows r r).toNat

/-- Run the per-row Schur scaled-coefficient kernel once and package both the
leading Gram determinant vector and the scaled Gram-Schmidt coefficient matrix. -/
@[expose]
def data (b : Matrix Int n m) : Data n :=
  let rows := scaledCoeffRowsSchur b
  { d := gramDetVecFromScaledCoeffRows rows
    ν := rowsToMatrix rows n }

/-- All leading Gram determinants, starting with the empty-prefix value
`d₀ = 1`. -/
@[expose]
def gramDetVec (b : Matrix Int n m) : Vector Nat (n + 1) :=
  (data b).d

/-- Integral scaled Gram-Schmidt coefficients. For `j < i`, the entry is the
determinant formula corresponding to `d_{j+1} * μ_{i,j}`; on the diagonal we
store `d_{j+1}`, and entries above the diagonal are zero. -/
@[expose]
def scaledCoeffs (b : Matrix Int n m) : Matrix Int n n :=
  (data b).ν

/-- Entry-level packaging equation from the public scaled-coefficient matrix
back to the shared array pass that computes it. -/
theorem scaledCoeffs_entry_eq_getArrayEntry
    (b : Matrix Int n m) (i j : Fin n) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      getArrayEntry (scaledCoeffRowsSchur b) i.val j.val := by
  simp [scaledCoeffs, data, rowsToMatrix, GramSchmidt.entry, Matrix.row, Matrix.ofFn]

/-- One Bareiss update step commutes with taking the leading `K × K`
prefix: the leading prefix of the updated full matrix equals the result
of running the same step on the leading prefix. The pivot/`prevPivot`
scalars are passed through unchanged. -/
private theorem leadingPrefix_stepMatrix_eq
    {n K : Nat} (M : Matrix Int n n) (hK : K ≤ n)
    (k : Nat) (pivot prevPivot : Int) :
    Matrix.leadingPrefix (Matrix.stepMatrix M k pivot prevPivot) K hK =
      Matrix.stepMatrix (Matrix.leadingPrefix M K hK) k pivot prevPivot := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let iK : Fin K := ⟨i, hi⟩
  let jK : Fin K := ⟨j, hj⟩
  let iN : Fin n := ⟨i, Nat.lt_of_lt_of_le hi hK⟩
  let jN : Fin n := ⟨j, Nat.lt_of_lt_of_le hj hK⟩
  show (Matrix.leadingPrefix (Matrix.stepMatrix M k pivot prevPivot) K hK)[iK][jK] =
      (Matrix.stepMatrix (Matrix.leadingPrefix M K hK) k pivot prevPivot)[iK][jK]
  simp only [Matrix.leadingPrefix_entry]
  show (Matrix.stepMatrix M k pivot prevPivot)[iN][jN] =
      (Matrix.stepMatrix (Matrix.leadingPrefix M K hK) k pivot prevPivot)[iK][jK]
  by_cases htrail : k < i ∧ k < j
  · have hki_n : k < iN.val := htrail.1
    have hkj_n : k < jN.val := htrail.2
    have hki_K : k < iK.val := htrail.1
    have hkj_K : k < jK.val := htrail.2
    rw [Matrix.stepMatrix_update_eq M k pivot prevPivot iN jN hki_n hkj_n]
    rw [Matrix.stepMatrix_update_eq (Matrix.leadingPrefix M K hK) k pivot prevPivot
      iK jK hki_K hkj_K]
    simp only [Matrix.leadingPrefix_entry]
    rfl
  · by_cases hbelow : k < i ∧ j = k
    · have hki_n : k < iN.val := hbelow.1
      have hjk_n : jN.val = k := hbelow.2
      have hki_K : k < iK.val := hbelow.1
      have hjk_K : jK.val = k := hbelow.2
      rw [Matrix.stepMatrix_pivot_col_below M k pivot prevPivot iN jN hki_n hjk_n]
      rw [Matrix.stepMatrix_pivot_col_below (Matrix.leadingPrefix M K hK) k
        pivot prevPivot iK jK hki_K hjk_K]
    · have hnot_n : ¬ (k < iN.val ∧ k < jN.val) := htrail
      have hnot_n' : ¬ (k < iN.val ∧ jN.val = k) := hbelow
      have hnot_K : ¬ (k < iK.val ∧ k < jK.val) := htrail
      have hnot_K' : ¬ (k < iK.val ∧ jK.val = k) := hbelow
      rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot iN jN hnot_n hnot_n']
      rw [Matrix.stepMatrix_eq_of_not_update (Matrix.leadingPrefix M K hK) k
        pivot prevPivot iK jK hnot_K hnot_K']
      simp only [Matrix.leadingPrefix_entry]
      rfl

/-- A bordered-minor entry equals the source matrix at the lifted index.
The lifted index for a row/column of the bordered minor is the bordered
"row"/"col" anchor when the bordered-minor coordinate hits the last
position (val = k) and the natural inclusion otherwise. -/
private theorem borderedMinor_entry_eq_source
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (i_bm j_bm : Fin (k + 1)) :
    (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] =
      M[(if h : i_bm.val < k then ⟨i_bm.val, Nat.lt_trans h hk⟩ else row)][
        (if h : j_bm.val < k then ⟨j_bm.val, Nat.lt_trans h hk⟩ else col)] := by
  by_cases hi_lt : i_bm.val < k
  · by_cases hj_lt : j_bm.val < k
    · have h := Matrix.borderedMinor_entry_lt_lt M k hk row col i_bm j_bm hi_lt hj_lt
      simp [hi_lt, hj_lt] at h ⊢
      exact h
    · have hj_eq : j_bm.val = k := by
        have := j_bm.isLt
        omega
      have hjFin : j_bm = Fin.last k := Fin.ext (by simp [hj_eq])
      have h := Matrix.borderedMinor_entry_lt_last M k hk row col i_bm hi_lt
      rw [hjFin]
      simp [hi_lt] at h ⊢
      exact h
  · have hi_eq : i_bm.val = k := by
      have := i_bm.isLt
      omega
    have hiFin : i_bm = Fin.last k := Fin.ext (by simp [hi_eq])
    by_cases hj_lt : j_bm.val < k
    · have h := Matrix.borderedMinor_entry_last_lt M k hk row col j_bm hj_lt
      rw [hiFin]
      simp [hj_lt] at h ⊢
      exact h
    · have hj_eq : j_bm.val = k := by
        have := j_bm.isLt
        omega
      have hjFin : j_bm = Fin.last k := Fin.ext (by simp [hj_eq])
      have h := Matrix.borderedMinor_entry_last_last M k hk row col
      rw [hiFin, hjFin]
      simp at h ⊢
      exact h

/-- Promote a bordered-minor coordinate to its lifted index in `Fin n`. -/
private def liftBorderedIdx {n k : Nat} (hk : k < n) (anchor : Fin n) (x : Fin (k + 1)) :
    Fin n :=
  if h : x.val < k then ⟨x.val, Nat.lt_trans h hk⟩ else anchor

private theorem liftBorderedIdx_val_lt {n k : Nat} (hk : k < n) (anchor : Fin n)
    (x : Fin (k + 1)) (h : x.val < k) :
    liftBorderedIdx hk anchor x = ⟨x.val, Nat.lt_trans h hk⟩ := by
  simp [liftBorderedIdx, h]

private theorem liftBorderedIdx_val_eq_k {n k : Nat} (hk : k < n) (anchor : Fin n)
    (x : Fin (k + 1)) (h : x.val = k) :
    liftBorderedIdx hk anchor x = anchor := by
  have : ¬ x.val < k := fun h' => Nat.lt_irrefl _ (h ▸ h')
  simp [liftBorderedIdx, this]

private theorem liftBorderedIdx_at_kStep {n k : Nat} (hk : k < n) (anchor : Fin n)
    {k_step : Nat} (hkstep : k_step < k) (hkstep_lt_n : k_step < n)
    (hkstep_lt_k1 : k_step < k + 1) :
    liftBorderedIdx hk anchor ⟨k_step, hkstep_lt_k1⟩ = ⟨k_step, hkstep_lt_n⟩ := by
  show (if h : k_step < k then (⟨k_step, Nat.lt_trans h hk⟩ : Fin n) else anchor) =
    ⟨k_step, hkstep_lt_n⟩
  simp [hkstep]

private theorem borderedMinor_entry_eq_lift
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (i_bm j_bm : Fin (k + 1)) :
    (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] =
      M[liftBorderedIdx hk row i_bm][liftBorderedIdx hk col j_bm] := by
  rw [borderedMinor_entry_eq_source M k hk row col i_bm j_bm]
  rfl

/-- One Bareiss update step commutes with taking a bordered minor whose
border row/column indices `row`, `col` lie in the trailing block: the
bordered minor of the updated full matrix equals the result of running
the same step on the bordered minor. The pivot/`prevPivot` scalars are
passed through unchanged. -/
private theorem borderedMinor_stepMatrix_eq
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val)
    (k_step : Nat) (hkstep : k_step < k) (pivot prevPivot : Int) :
    Matrix.borderedMinor (Matrix.stepMatrix M k_step pivot prevPivot) k hk row col =
      Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let i_bm : Fin (k + 1) := ⟨i, hi⟩
  let j_bm : Fin (k + 1) := ⟨j, hj⟩
  let iN : Fin n := liftBorderedIdx hk row i_bm
  let jN : Fin n := liftBorderedIdx hk col j_bm
  -- Equivalence of "in update zone" between bordered minor and source.
  have hi_iff : k_step < i_bm.val ↔ k_step < iN.val := by
    by_cases hi_lt : i_bm.val < k
    · have : iN = ⟨i_bm.val, Nat.lt_trans hi_lt hk⟩ :=
        liftBorderedIdx_val_lt hk row i_bm hi_lt
      rw [show iN.val = i_bm.val from congrArg Fin.val this]
    · have hi_eq : i_bm.val = k := by have := i_bm.isLt; omega
      have : iN = row := liftBorderedIdx_val_eq_k hk row i_bm hi_eq
      rw [show iN.val = row.val from congrArg Fin.val this, hi_eq]
      constructor
      · intro _; exact Nat.lt_of_lt_of_le hkstep hrow
      · intro _; exact hkstep
  have hj_iff : k_step < j_bm.val ↔ k_step < jN.val := by
    by_cases hj_lt : j_bm.val < k
    · have : jN = ⟨j_bm.val, Nat.lt_trans hj_lt hk⟩ :=
        liftBorderedIdx_val_lt hk col j_bm hj_lt
      rw [show jN.val = j_bm.val from congrArg Fin.val this]
    · have hj_eq : j_bm.val = k := by have := j_bm.isLt; omega
      have : jN = col := liftBorderedIdx_val_eq_k hk col j_bm hj_eq
      rw [show jN.val = col.val from congrArg Fin.val this, hj_eq]
      constructor
      · intro _; exact Nat.lt_of_lt_of_le hkstep hcol
      · intro _; exact hkstep
  have hj_eq_iff : j_bm.val = k_step ↔ jN.val = k_step := by
    by_cases hj_lt : j_bm.val < k
    · have : jN = ⟨j_bm.val, Nat.lt_trans hj_lt hk⟩ :=
        liftBorderedIdx_val_lt hk col j_bm hj_lt
      rw [show jN.val = j_bm.val from congrArg Fin.val this]
    · have hj_eq : j_bm.val = k := by have := j_bm.isLt; omega
      have : jN = col := liftBorderedIdx_val_eq_k hk col j_bm hj_eq
      rw [show jN.val = col.val from congrArg Fin.val this, hj_eq]
      constructor
      · intro h; omega
      · intro h; exact absurd h (Nat.ne_of_gt (Nat.lt_of_lt_of_le hkstep hcol))
  -- Identify: borderedMinor entry at (i_bm, j_bm) equals M entry at (iN, jN).
  have h_entry : ∀ (M' : Matrix Int n n) (r : Fin (k + 1)) (c : Fin (k + 1)),
      (Matrix.borderedMinor M' k hk row col)[r][c] =
        M'[liftBorderedIdx hk row r][liftBorderedIdx hk col c] :=
    fun M' r c => borderedMinor_entry_eq_lift M' k hk row col r c
  show (Matrix.borderedMinor (Matrix.stepMatrix M k_step pivot prevPivot) k hk row col)[i_bm][j_bm] =
       (Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot)[i_bm][j_bm]
  rw [h_entry (Matrix.stepMatrix M k_step pivot prevPivot) i_bm j_bm]
  -- LHS = (stepMatrix M k_step pivot prevPivot)[iN][jN].
  by_cases htrail_bm : k_step < i_bm.val ∧ k_step < j_bm.val
  · have htrail_N : k_step < iN.val ∧ k_step < jN.val :=
      ⟨hi_iff.mp htrail_bm.1, hj_iff.mp htrail_bm.2⟩
    -- Pivot column / pivot row indices in `Fin (k+1)` have val = k_step < k.
    have hkstep_lt_k1 : k_step < k + 1 := Nat.lt_succ_of_lt hkstep
    have hkstep_lt_n : k_step < n := Nat.lt_trans hkstep hk
    let colK_bm : Fin (k + 1) := ⟨k_step, hkstep_lt_k1⟩
    let colK_N : Fin n := ⟨k_step, hkstep_lt_n⟩
    have hcolK_row : liftBorderedIdx hk row colK_bm = colK_N :=
      liftBorderedIdx_at_kStep hk row hkstep hkstep_lt_n hkstep_lt_k1
    have hcolK_col : liftBorderedIdx hk col colK_bm = colK_N :=
      liftBorderedIdx_at_kStep hk col hkstep hkstep_lt_n hkstep_lt_k1
    have h_iK : (Matrix.borderedMinor M k hk row col)[i_bm][colK_bm] = M[iN][colK_N] := by
      rw [h_entry M i_bm colK_bm]
      show M[iN][liftBorderedIdx hk col colK_bm] = M[iN][colK_N]
      exact congrArg (fun (x : Fin n) => M[iN][x]) hcolK_col
    have h_Kj : (Matrix.borderedMinor M k hk row col)[colK_bm][j_bm] = M[colK_N][jN] := by
      rw [h_entry M colK_bm j_bm]
      show M[liftBorderedIdx hk row colK_bm][jN] = M[colK_N][jN]
      exact congrArg (fun (x : Fin n) => M[x][jN]) hcolK_row
    -- Compute LHS directly.
    have hLHS :
        (Matrix.stepMatrix M k_step pivot prevPivot)[iN][jN] =
          Matrix.exactDiv (pivot * M[iN][jN] -
            M[iN][colK_N] * M[colK_N][jN]) prevPivot := by
      rw [Matrix.stepMatrix_update_eq M k_step pivot prevPivot iN jN htrail_N.1 htrail_N.2]
    have hRHS :
        (Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot)[i_bm][j_bm] =
          Matrix.exactDiv (pivot * (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] -
            (Matrix.borderedMinor M k hk row col)[i_bm][colK_bm] *
            (Matrix.borderedMinor M k hk row col)[colK_bm][j_bm]) prevPivot := by
      rw [Matrix.stepMatrix_update_eq (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot
        i_bm j_bm htrail_bm.1 htrail_bm.2]
    rw [hLHS, hRHS, h_entry M i_bm j_bm, h_iK, h_Kj]
  · by_cases hbelow_bm : k_step < i_bm.val ∧ j_bm.val = k_step
    · have hi_N : k_step < iN.val := hi_iff.mp hbelow_bm.1
      have hj_N : jN.val = k_step := hj_eq_iff.mp hbelow_bm.2
      rw [Matrix.stepMatrix_pivot_col_below M k_step pivot prevPivot iN jN hi_N hj_N]
      rw [Matrix.stepMatrix_pivot_col_below (Matrix.borderedMinor M k hk row col) k_step
        pivot prevPivot i_bm j_bm hbelow_bm.1 hbelow_bm.2]
    · -- Outside the update zone on both sides.
      have hnot_trail_N : ¬ (k_step < iN.val ∧ k_step < jN.val) := by
        intro h
        exact htrail_bm ⟨hi_iff.mpr h.1, hj_iff.mpr h.2⟩
      have hnot_below_N : ¬ (k_step < iN.val ∧ jN.val = k_step) := by
        intro h
        exact hbelow_bm ⟨hi_iff.mpr h.1, hj_eq_iff.mpr h.2⟩
      rw [Matrix.stepMatrix_eq_of_not_update M k_step pivot prevPivot iN jN
        hnot_trail_N hnot_below_N]
      rw [Matrix.stepMatrix_eq_of_not_update (Matrix.borderedMinor M k hk row col) k_step
        pivot prevPivot i_bm j_bm htrail_bm hbelow_bm]
      exact (h_entry M i_bm j_bm).symm

/-- Run `noPivotLoop` on a full `n × n` matrix and on its `(k + 1) × (k + 1)`
bordered minor (whose border row/column indices `row`, `col` lie in the
trailing block) from two BareissStates that agree under the bordered
minor. While both runs are still synchronized (`fuel + state.step < k + 1`),
their bookkeeping fields agree and the full state's matrix, restricted
to the bordered minor, matches the bordered-minor state's matrix. -/
private theorem noPivotLoop_sync_borderedMinor_aux
    {n : Nat} (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val) (fuel : Nat) :
    ∀ (state_full : Matrix.BareissState n) (state_bm : Matrix.BareissState (k + 1)),
      state_full.step = state_bm.step →
      state_full.prevPivot = state_bm.prevPivot →
      state_full.rowSwaps = state_bm.rowSwaps →
      state_full.singularStep = state_bm.singularStep →
      Matrix.borderedMinor state_full.matrix k hk row col = state_bm.matrix →
      fuel + state_full.step < k + 1 →
      (Matrix.noPivotLoop fuel state_full).step =
          (Matrix.noPivotLoop fuel state_bm).step ∧
      (Matrix.noPivotLoop fuel state_full).prevPivot =
          (Matrix.noPivotLoop fuel state_bm).prevPivot ∧
      (Matrix.noPivotLoop fuel state_full).rowSwaps =
          (Matrix.noPivotLoop fuel state_bm).rowSwaps ∧
      (Matrix.noPivotLoop fuel state_full).singularStep =
          (Matrix.noPivotLoop fuel state_bm).singularStep ∧
      Matrix.borderedMinor (Matrix.noPivotLoop fuel state_full).matrix k hk row col =
          (Matrix.noPivotLoop fuel state_bm).matrix := by
  induction fuel with
  | zero =>
      intros state_full state_bm h_step h_prev h_rows h_sing h_mat _hfuel
      simp only [Matrix.noPivotLoop]
      exact ⟨h_step, h_prev, h_rows, h_sing, h_mat⟩
  | succ f ih =>
      intros state_full state_bm h_step h_prev h_rows h_sing h_mat hfuel
      have h_step_lt_k1 : state_full.step + 1 < k + 1 := by omega
      have h_step_lt_k : state_full.step < k := by omega
      have h_step_lt_n : state_full.step < n := Nat.lt_trans h_step_lt_k hk
      have h_full_done : state_full.step + 1 < n := by
        have hk_le : k + 1 ≤ n := Nat.succ_le_of_lt hk
        omega
      have h_bm_done : state_bm.step + 1 < k + 1 := h_step ▸ h_step_lt_k1
      have h_bm_step_lt_k : state_bm.step < k := h_step ▸ h_step_lt_k
      let k_full : Fin n := ⟨state_full.step, h_step_lt_n⟩
      let k_bm : Fin (k + 1) := ⟨state_bm.step, Nat.lt_succ_of_lt h_bm_step_lt_k⟩
      have h_k_bm_lt : k_bm.val < k := h_bm_step_lt_k
      -- Pivot entries agree because borderedMinor of full state's matrix equals bm state's matrix.
      have h_pivot_eq :
          state_full.matrix[k_full][k_full] = state_bm.matrix[k_bm][k_bm] := by
        have hcongr :
            (Matrix.borderedMinor state_full.matrix k hk row col)[k_bm][k_bm] =
              state_bm.matrix[k_bm][k_bm] := by rw [h_mat]
        have h_bm_entry :=
          Matrix.borderedMinor_entry_lt_lt state_full.matrix k hk row col k_bm k_bm
            h_k_bm_lt h_k_bm_lt
        simp only at h_bm_entry
        rw [h_bm_entry] at hcongr
        have h_idx : k_full = (⟨k_bm.val, Nat.lt_trans h_k_bm_lt hk⟩ : Fin n) :=
          Fin.ext h_step
        calc state_full.matrix[k_full][k_full]
            = state_full.matrix[(⟨k_bm.val, Nat.lt_trans h_k_bm_lt hk⟩ : Fin n)][
                (⟨k_bm.val, Nat.lt_trans h_k_bm_lt hk⟩ : Fin n)] :=
              congrArg (fun (i : Fin n) => state_full.matrix[i][i]) h_idx
          _ = state_bm.matrix[k_bm][k_bm] := hcongr
      by_cases hp_full : state_full.matrix[k_full][k_full] = 0
      · -- Singular branch on both sides.
        have hp_bm : state_bm.matrix[k_bm][k_bm] = 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_singular_branch f state_full h_full_done hp_full]
        rw [Matrix.noPivotLoop_singular_branch f state_bm h_bm_done hp_bm]
        refine ⟨h_step, h_prev, h_rows, ?_, h_mat⟩
        simp [h_step]
      · -- Regular branch on both sides; apply IH to the updated states.
        have hp_bm : state_bm.matrix[k_bm][k_bm] ≠ 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_regular_branch f state_full h_full_done hp_full]
        rw [Matrix.noPivotLoop_regular_branch f state_bm h_bm_done hp_bm]
        have h_new_mat :
            Matrix.borderedMinor
              (Matrix.stepMatrix state_full.matrix state_full.step
                state_full.matrix[k_full][k_full] state_full.prevPivot) k hk row col =
              Matrix.stepMatrix state_bm.matrix state_bm.step
                state_bm.matrix[k_bm][k_bm] state_bm.prevPivot := by
          rw [borderedMinor_stepMatrix_eq state_full.matrix k hk row col hrow hcol
              state_full.step h_step_lt_k state_full.matrix[k_full][k_full]
              state_full.prevPivot, h_mat, h_step, h_prev, h_pivot_eq]
        apply ih
        · -- step
          simp [h_step]
        · -- prevPivot
          exact h_pivot_eq
        · -- rowSwaps
          exact h_rows
        · -- singularStep
          rfl
        · -- matrix
          exact h_new_mat
        · -- fuel
          simp; omega

/-- The `(row, col)` entry of the noPivot Bareiss state after `k` iterations on
the full `n × n` matrix agrees with the `(Fin.last k, Fin.last k)` entry of the
noPivot Bareiss state after `k` iterations on the `(k + 1) × (k + 1)` bordered
minor at `row, col`. The `singularStep` bookkeeping also agrees, mirroring the
leading-prefix sync corollary. Requires `row, col` to lie in the trailing block. -/
theorem noPivotLoop_full_eq_borderedMinor_at_trailing
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val) :
    let BM := Matrix.borderedMinor M k hk row col
    let s_full := Matrix.noPivotLoop k (Matrix.noPivotInitialState M)
    let s_bm := Matrix.noPivotLoop k (Matrix.noPivotInitialState BM)
    s_full.matrix[row][col] = s_bm.matrix[Fin.last k][Fin.last k] ∧
      s_full.singularStep = s_bm.singularStep := by
  intro BM s_full s_bm
  have h_sync :=
    noPivotLoop_sync_borderedMinor_aux k hk row col hrow hcol k
      (Matrix.noPivotInitialState M) (Matrix.noPivotInitialState BM)
      rfl rfl rfl rfl rfl
      (show k + (Matrix.noPivotInitialState M).step < k + 1 by
        simp [Matrix.noPivotInitialState])
  obtain ⟨_, _, _, h_sing, h_mat⟩ := h_sync
  refine ⟨?_, h_sing⟩
  -- The (row, col) entry of s_full.matrix is the (Fin.last k, Fin.last k) entry of
  -- (borderedMinor s_full.matrix k hk row col), which equals s_bm.matrix by `h_mat`.
  have hcongr :
      (Matrix.borderedMinor s_full.matrix k hk row col)[Fin.last k][Fin.last k] =
        s_bm.matrix[Fin.last k][Fin.last k] := by rw [h_mat]
  rw [Matrix.borderedMinor_entry_last_last] at hcongr
  exact hcongr

/-- The step field of a no-pivot Bareiss state advances by at most `fuel` after
`fuel` loop iterations. Combined with `noPivotLoop_step_monotone`, this brackets
the resulting step between the starting step and the starting step plus the
fuel. -/
private theorem noPivotLoop_step_le_add
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n) :
    (Matrix.noPivotLoop fuel state).step ≤ state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step ≤ state.step + 0
      omega
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          show state.step ≤ state.step + (f + 1)
          omega
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          calc (Matrix.noPivotLoop f
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }).step
              ≤ state.step + 1 + f := ih _
            _ = state.step + (f + 1) := by omega
      · rw [Matrix.noPivotLoop_done f state hDone]
        show state.step ≤ state.step + (f + 1)
        omega

/-- Trailing-block symmetry is preserved by the no-pivot Bareiss loop: if the
input state's matrix is symmetric at indices at or beyond `state.step`, then the
resulting state's matrix is symmetric at indices at or beyond its `step`. The
abstract version takes only the input symmetry hypothesis; the diagonal Bareiss
update commutes through symmetry because the trailing block remains symmetric
after each `stepMatrix` application. -/
private theorem noPivotLoop_matrix_symm_preserve
    {n : Nat} (fuel : Nat) :
    ∀ (state : Matrix.BareissState n),
      (∀ a b : Fin n, state.step ≤ a.val → state.step ≤ b.val →
        state.matrix[a][b] = state.matrix[b][a]) →
      ∀ (a b : Fin n),
        (Matrix.noPivotLoop fuel state).step ≤ a.val →
        (Matrix.noPivotLoop fuel state).step ≤ b.val →
        (Matrix.noPivotLoop fuel state).matrix[a][b] =
          (Matrix.noPivotLoop fuel state).matrix[b][a] := by
  induction fuel with
  | zero =>
      intros state h_sym a b ha hb
      change state.matrix[a][b] = state.matrix[b][a]
      change state.step ≤ a.val at ha
      change state.step ≤ b.val at hb
      exact h_sym a b ha hb
  | succ f ih =>
      intros state h_sym a b ha hb
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · -- Singular branch: result is `{state with singularStep := some state.step}`.
          rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at ha hb ⊢
          change state.matrix[a][b] = state.matrix[b][a]
          change state.step ≤ a.val at ha
          change state.step ≤ b.val at hb
          exact h_sym a b ha hb
        · -- Regular branch: recurse on the updated state with step + 1.
          rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at ha hb ⊢
          let kFin : Fin n := ⟨state.step, Nat.lt_of_succ_lt hDone⟩
          have h_sym_new : ∀ (a' b' : Fin n),
              state.step + 1 ≤ a'.val → state.step + 1 ≤ b'.val →
              (Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot)[a'][b']
                = (Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot)[b'][a'] := by
            intros a' b' ha' hb'
            have ha'_lt : state.step < a'.val := ha'
            have hb'_lt : state.step < b'.val := hb'
            rw [Matrix.stepMatrix_update_eq state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot a' b' ha'_lt hb'_lt]
            rw [Matrix.stepMatrix_update_eq state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot b' a' hb'_lt ha'_lt]
            -- Both sides reduce to `exactDiv` of similar expressions. Identify
            -- the two `Fin n` indices at value `state.step` and use the
            -- trailing-block symmetry of `state.matrix`.
            have h_ab : state.matrix[a'][b'] = state.matrix[b'][a'] :=
              h_sym a' b' (Nat.le_of_lt ha'_lt) (Nat.le_of_lt hb'_lt)
            have h_ak : state.matrix[a'][kFin] = state.matrix[kFin][a'] :=
              h_sym a' kFin (Nat.le_of_lt ha'_lt) (Nat.le_refl _)
            have h_bk : state.matrix[b'][kFin] = state.matrix[kFin][b'] :=
              h_sym b' kFin (Nat.le_of_lt hb'_lt) (Nat.le_refl _)
            -- The two `Fin n` indices in the unfolded `stepMatrix_update_eq`
            -- have value `state.step` and so equal `kFin` definitionally.
            change Matrix.exactDiv (_ * state.matrix[a'][b']
                - state.matrix[a'][kFin] * state.matrix[kFin][b']) _
              = Matrix.exactDiv (_ * state.matrix[b'][a']
                - state.matrix[b'][kFin] * state.matrix[kFin][a']) _
            rw [h_ab, h_ak, h_bk]
            congr 1
            grind
          exact ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            (by
              intros a' b' ha' hb'
              exact h_sym_new a' b' ha' hb')
            a b ha hb
      · -- Boundary case: `noPivotLoop` returns the input state unchanged.
        rw [Matrix.noPivotLoop_done f state hDone] at ha hb ⊢
        change state.matrix[a][b] = state.matrix[b][a]
        change state.step ≤ a.val at ha
        change state.step ≤ b.val at hb
        exact h_sym a b ha hb

/-- Identification of Bareiss-style trailing values across two bordered minors
of a symmetric matrix obtained by swapping the border row and column. Composed from
`noPivotLoop_full_eq_borderedMinor_at_trailing` (applied at both swapped
positions) and `noPivotLoop_matrix_symm_preserve` (which transports the
trailing-block symmetry of the input through the loop). -/
private theorem noPivotLoop_borderedMinor_swap_at_trailing
    {n : Nat} (M : Matrix Int n n)
    (h_sym : ∀ a b : Fin n, M[a][b] = M[b][a])
    (k : Nat) (hk : k < n) (i j : Fin n)
    (hki : k ≤ i.val) (hkj : k ≤ j.val) :
    (Matrix.noPivotLoop k (Matrix.noPivotInitialState
        (Matrix.borderedMinor M k hk i j))).matrix[Fin.last k][Fin.last k] =
    (Matrix.noPivotLoop k (Matrix.noPivotInitialState
        (Matrix.borderedMinor M k hk j i))).matrix[Fin.last k][Fin.last k] := by
  -- Reduce both sides through the full-matrix sync at swapped border positions.
  have h_ij :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing M k hk i j hki hkj).1
  have h_ji :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing M k hk j i hkj hki).1
  rw [← h_ij, ← h_ji]
  -- Reduce to symmetry of the full-matrix noPivotLoop at `(i, j)` vs `(j, i)`.
  -- Both indices are bounded below by `k`, and the loop's resulting step is at
  -- most `0 + k = k`, hence at most each of `i.val`, `j.val`.
  have h_step_le := noPivotLoop_step_le_add k (Matrix.noPivotInitialState M)
  have h_step0 : (Matrix.noPivotInitialState M).step = 0 := rfl
  have h_step_bound :
      (Matrix.noPivotLoop k (Matrix.noPivotInitialState M)).step ≤ k := by
    rw [h_step0] at h_step_le
    simpa using h_step_le
  have h_init_sym :
      ∀ a b : Fin n, (Matrix.noPivotInitialState M).step ≤ a.val →
        (Matrix.noPivotInitialState M).step ≤ b.val →
        (Matrix.noPivotInitialState M).matrix[a][b] =
          (Matrix.noPivotInitialState M).matrix[b][a] := by
    intros a b _ _
    exact h_sym a b
  exact noPivotLoop_matrix_symm_preserve k
    (Matrix.noPivotInitialState M) h_init_sym i j
    (Nat.le_trans h_step_bound hki) (Nat.le_trans h_step_bound hkj)

/-- Run `noPivotLoop` on a full `n × n` matrix and on its `K × K` leading
prefix from two BareissStates that agree on the leading prefix. While
both runs are still synchronized (fuel fits within `K - state.step`),
their bookkeeping fields agree and the full state's matrix, restricted
to the leading prefix, matches the prefix state's matrix. -/
private theorem noPivotLoop_sync_leadingPrefix_aux
    {n K : Nat} (hK : K ≤ n) (fuel : Nat) :
    ∀ (state_full : Matrix.BareissState n) (state_pref : Matrix.BareissState K),
      state_full.step = state_pref.step →
      state_full.prevPivot = state_pref.prevPivot →
      state_full.rowSwaps = state_pref.rowSwaps →
      state_full.singularStep = state_pref.singularStep →
      Matrix.leadingPrefix state_full.matrix K hK = state_pref.matrix →
      fuel + state_full.step < K →
      (Matrix.noPivotLoop fuel state_full).step =
          (Matrix.noPivotLoop fuel state_pref).step ∧
      (Matrix.noPivotLoop fuel state_full).prevPivot =
          (Matrix.noPivotLoop fuel state_pref).prevPivot ∧
      (Matrix.noPivotLoop fuel state_full).rowSwaps =
          (Matrix.noPivotLoop fuel state_pref).rowSwaps ∧
      (Matrix.noPivotLoop fuel state_full).singularStep =
          (Matrix.noPivotLoop fuel state_pref).singularStep ∧
      Matrix.leadingPrefix (Matrix.noPivotLoop fuel state_full).matrix K hK =
          (Matrix.noPivotLoop fuel state_pref).matrix := by
  induction fuel with
  | zero =>
      intros state_full state_pref h_step h_prev h_rows h_sing h_mat _hfuel
      simp only [Matrix.noPivotLoop]
      exact ⟨h_step, h_prev, h_rows, h_sing, h_mat⟩
  | succ f ih =>
      intros state_full state_pref h_step h_prev h_rows h_sing h_mat hfuel
      have h_step_lt_K : state_full.step + 1 < K := by omega
      have h_full_done : state_full.step + 1 < n :=
        Nat.lt_of_lt_of_le h_step_lt_K hK
      have h_pref_done : state_pref.step + 1 < K := h_step ▸ h_step_lt_K
      have h_step_lt_n : state_full.step < n := Nat.lt_of_succ_lt h_full_done
      have h_step_lt_K_strict : state_full.step < K :=
        Nat.lt_of_succ_lt h_step_lt_K
      have h_pref_step_lt_K : state_pref.step < K := h_step ▸ h_step_lt_K_strict
      let k_full : Fin n := ⟨state_full.step, h_step_lt_n⟩
      let k_pref : Fin K := ⟨state_pref.step, h_pref_step_lt_K⟩
      let k_full' : Fin K := ⟨state_full.step, h_step_lt_K_strict⟩
      -- The pivot entries agree on both sides because the full state's
      -- matrix, restricted to the leading prefix, equals the prefix state's
      -- matrix.
      have h_k_eq : k_full' = k_pref := Fin.ext h_step
      have h_pivot_eq : state_full.matrix[k_full][k_full] =
          state_pref.matrix[k_pref][k_pref] := by
        have hcongr := congrArg (fun (M : Matrix Int K K) => M[k_pref][k_pref]) h_mat
        simp only [Matrix.leadingPrefix_entry] at hcongr
        -- hcongr : state_full.matrix[⟨k_pref.val, _⟩][⟨k_pref.val, _⟩] =
        --          state_pref.matrix[k_pref][k_pref]
        -- k_full.val = state_full.step = state_pref.step = k_pref.val (by h_step),
        -- so as Fin n elements they coincide. Use congrArg on the diagonal
        -- entry as a function of Fin n to close the gap.
        have h_idx :
            k_full = (⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n) :=
          Fin.ext h_step
        have h_diag :
            state_full.matrix[k_full][k_full] =
              state_full.matrix[(⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n)][(⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n)] :=
          congrArg (fun (i : Fin n) => state_full.matrix[i][i]) h_idx
        exact h_diag.trans hcongr
      by_cases hp_full : state_full.matrix[k_full][k_full] = 0
      · -- Singular branch on both sides.
        have hp_pref : state_pref.matrix[k_pref][k_pref] = 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_singular_branch f state_full h_full_done hp_full]
        rw [Matrix.noPivotLoop_singular_branch f state_pref h_pref_done hp_pref]
        refine ⟨h_step, h_prev, h_rows, ?_, h_mat⟩
        simp [h_step]
      · -- Regular branch on both sides; apply IH to the updated states.
        have hp_pref : state_pref.matrix[k_pref][k_pref] ≠ 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_regular_branch f state_full h_full_done hp_full]
        rw [Matrix.noPivotLoop_regular_branch f state_pref h_pref_done hp_pref]
        -- After one step, the new states are still linked.
        have h_new_mat :
            Matrix.leadingPrefix
              (Matrix.stepMatrix state_full.matrix state_full.step
                state_full.matrix[k_full][k_full] state_full.prevPivot) K hK =
              Matrix.stepMatrix state_pref.matrix state_pref.step
                state_pref.matrix[k_pref][k_pref] state_pref.prevPivot := by
          rw [leadingPrefix_stepMatrix_eq, h_mat, h_step, h_prev, h_pivot_eq]
        apply ih
        · -- step
          simp [h_step]
        · -- prevPivot
          exact h_pivot_eq
        · -- rowSwaps
          exact h_rows
        · -- singularStep
          rfl
        · -- matrix
          exact h_new_mat
        · -- fuel
          simp; omega

/-- Once the no-pivot Bareiss loop has reached the boundary
(`state.step + 1 ≥ n`), any further fuel is a no-op. -/
private theorem noPivotLoop_id_at_done
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (hDone : ¬ state.step + 1 < n) :
    Matrix.noPivotLoop fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih => exact Matrix.noPivotLoop_done f state hDone

/-- Once the no-pivot Bareiss loop has marked the current step singular
(`state.singularStep = some state.step` with a zero pivot at that step),
any further fuel is a no-op. -/
theorem noPivotLoop_id_at_singular_fixedpoint
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0)
    (hsing : state.singularStep = some state.step) :
    Matrix.noPivotLoop fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih =>
      rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
      -- Goal: {state with singularStep := some state.step} = state.
      cases state with
      | mk step matrix prevPivot rowSwaps singularStep =>
        simp only at hsing
        subst hsing
        rfl

/-- Fuel composition for the no-pivot Bareiss loop: running `a + b` units of
fuel from `state` equals running `b` more units after `a` initial units. -/
theorem noPivotLoop_add
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n) :
    Matrix.noPivotLoop (a + b) state =
      Matrix.noPivotLoop b (Matrix.noPivotLoop a state) := by
  induction a generalizing state with
  | zero =>
      show Matrix.noPivotLoop (0 + b) state = Matrix.noPivotLoop b state
      simp
  | succ a' ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · -- Singular: both sides collapse to `{state with singularStep := some state.step}`.
          have h_lhs :
              Matrix.noPivotLoop (a' + 1 + b) state =
                {state with singularStep := some state.step} := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact Matrix.noPivotLoop_singular_branch (a' + b) state hDone hp
          have h_rhs_inner :
              Matrix.noPivotLoop (a' + 1) state =
                {state with singularStep := some state.step} :=
            Matrix.noPivotLoop_singular_branch a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          symm
          -- Now show: noPivotLoop b {state with singularStep := some state.step} = that.
          let s' : Matrix.BareissState n :=
            {state with singularStep := some state.step}
          have hDone_s' : s'.step + 1 < n := hDone
          have hp_s' : s'.matrix[(⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)][(⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)] = 0 := hp
          have hsing_s' : s'.singularStep = some s'.step := rfl
          exact noPivotLoop_id_at_singular_fixedpoint b s' hDone_s' hp_s' hsing_s'
        · -- Regular: both sides do one step then recurse on `next`.
          have h_lhs :
              Matrix.noPivotLoop (a' + 1 + b) state =
                Matrix.noPivotLoop (a' + b)
                  { step := state.step + 1
                    matrix := Matrix.stepMatrix state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact Matrix.noPivotLoop_regular_branch (a' + b) state hDone hp
          have h_rhs_inner :
              Matrix.noPivotLoop (a' + 1) state =
                Matrix.noPivotLoop a'
                  { step := state.step + 1
                    matrix := Matrix.stepMatrix state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } :=
            Matrix.noPivotLoop_regular_branch a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          exact ih _
      · -- Boundary: both sides return `state` unchanged.
        rw [noPivotLoop_id_at_done (a' + 1 + b) state hDone]
        rw [noPivotLoop_id_at_done (a' + 1) state hDone]
        exact (noPivotLoop_id_at_done b state hDone).symm

/-- After running `noPivotLoop` from a state without a recorded singular
step, the result has either no singular step, or it has a singular step
that matches the current `step` field together with a zero pivot at that
position. -/
theorem noPivotLoop_singular_inv
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none) :
    (Matrix.noPivotLoop fuel state).singularStep = none ∨
    ∃ k : Fin n,
      (Matrix.noPivotLoop fuel state).singularStep = some k.val ∧
      (Matrix.noPivotLoop fuel state).step = k.val ∧
      (Matrix.noPivotLoop fuel state).matrix[k][k] = 0 ∧
      k.val + 1 < n := by
  induction fuel generalizing state with
  | zero =>
      left
      change state.singularStep = none
      exact h_init
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n := ⟨state.step, Nat.lt_of_succ_lt hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · -- Singular branch: result = {state with singularStep := some state.step}.
          right
          refine ⟨k, ?_, ?_, ?_, hDone⟩
          · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
            exact hp
        · -- Regular branch
          rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          exact ih _ rfl
      · -- Boundary
        rw [Matrix.noPivotLoop_done f state hDone]
        left; exact h_init

/-- When the no-pivot Bareiss loop starts from a non-singular state and records
a singular step within `fuel` iterations, the recorded singular index is
strictly bounded by the initial step plus the fuel. The singular branch sets
`singularStep := some state.step` at the trigger iteration, and `state.step`
advances by at most one per regular iteration; with `fuel` iterations available
and at least one used for the singular trigger, the recorded index is `< start
+ fuel`. -/
theorem noPivotLoop_singularStep_lt
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop fuel state).singularStep = some s) :
    s < state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      rw [Matrix.noPivotLoop_zero_fuel, h_init] at h_sing
      nomatch h_sing
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_sing
          simp at h_sing
          omega
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at h_sing
          have h_ih := ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            rfl h_sing
          change s < state.step + 1 + f at h_ih
          show s < state.step + (f + 1)
          omega
      · rw [Matrix.noPivotLoop_done f state hDone] at h_sing
        rw [h_init] at h_sing
        nomatch h_sing

/-- After running `fuel` iterations of `Matrix.noPivotLoop` from a state with
no recorded singular step, if the result also has no recorded singular step
and the loop had at least `fuel + 1` steps of room from its starting step,
then the result's step is the starting step plus `fuel`. -/
private theorem noPivotLoop_step_eq_add_of_singularStep_none
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none)
    (h_room : state.step + fuel + 1 ≤ n)
    (h_no_sing : (Matrix.noPivotLoop fuel state).singularStep = none) :
    (Matrix.noPivotLoop fuel state).step = state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step = state.step + 0
      omega
  | succ f ih =>
      have hDone : state.step + 1 < n := by omega
      by_cases hp : state.matrix[state.step][state.step] = 0
      · rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_no_sing
        simp at h_no_sing
      · rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at h_no_sing
        rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
        have h_next_room : state.step + 1 + f + 1 ≤ n := by omega
        have h_next_step := ih
          { step := state.step + 1
            matrix := Matrix.stepMatrix state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          rfl h_next_room h_no_sing
        rw [h_next_step]
        show state.step + 1 + f = state.step + (f + 1)
        omega

/-- A no-pivot Bareiss pass that never records a singular step preserves the
nonzero status of the previous pivot. Regular branches replace `prevPivot` by
the current nonzero pivot; singular branches contradict the final
`singularStep = none` hypothesis. -/
private theorem noPivotLoop_prevPivot_ne_zero
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (hprev : state.prevPivot ≠ 0)
    (h_no_sing : (Matrix.noPivotLoop fuel state).singularStep = none) :
    (Matrix.noPivotLoop fuel state).prevPivot ≠ 0 := by
  induction fuel generalizing state with
  | zero =>
      simpa [Matrix.noPivotLoop_zero_fuel] using hprev
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_no_sing
          simp at h_no_sing
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at h_no_sing
          rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          exact ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            hp h_no_sing
      · rw [Matrix.noPivotLoop_done f state hDone] at h_no_sing ⊢
        exact hprev

/-- The `step` field of a no-pivot Bareiss state never decreases under further
loop iterations. -/
theorem noPivotLoop_step_monotone
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n) :
    state.step ≤ (Matrix.noPivotLoop fuel state).step := by
  induction fuel generalizing state with
  | zero =>
      show state.step ≤ state.step
      omega
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · have hStepLt : state.step < n := Nat.lt_of_succ_lt hDone
        by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          show state.step ≤ state.step
          omega
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          have h_ih := ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          -- h_ih says state.step + 1 ≤ (noPivotLoop f next).step
          -- Want: state.step ≤ (noPivotLoop f next).step
          exact Nat.le_trans (Nat.le_succ _) h_ih
      · rw [Matrix.noPivotLoop_done f state hDone]
        show state.step ≤ state.step
        omega

/-- A singular step recorded by an initial no-pivot prefix remains the recorded
singular step after any further no-pivot iterations. -/
private theorem noPivotLoop_singularStep
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none) {s : Nat}
    (h_prefix : (Matrix.noPivotLoop a state).singularStep = some s) :
    (Matrix.noPivotLoop (a + b) state).singularStep = some s := by
  rw [noPivotLoop_add a b state]
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, h_step, h_zero, h_bound⟩
  · rw [h_none] at h_prefix
    nomatch h_prefix
  · have hs : s = k.val := by
      rw [h_sing] at h_prefix
      injection h_prefix with h
      exact h.symm
    have hDone :
        (Matrix.noPivotLoop a state).step + 1 < n := by
      rw [h_step]
      exact h_bound
    have hidx :
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step
    have hp :
        (Matrix.noPivotLoop a state).matrix[
            (⟨(Matrix.noPivotLoop a state).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)][
            (⟨(Matrix.noPivotLoop a state).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
      have h_lift := congrArg
        (fun (idx : Fin n) => (Matrix.noPivotLoop a state).matrix[idx][idx])
        hidx
      exact h_lift.trans h_zero
    have hsing_state :
        (Matrix.noPivotLoop a state).singularStep =
          some (Matrix.noPivotLoop a state).step := by
      rw [h_sing, h_step]
    rw [noPivotLoop_id_at_singular_fixedpoint b _ hDone hp hsing_state]
    rw [hs]
    exact h_sing

/-- If a full no-pivot run has no singular step, every initial prefix run also
has no singular step. -/
private theorem noPivotLoop_prefix_none_of_final_none
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none)
    (h_final : (Matrix.noPivotLoop (a + b) state).singularStep = none) :
    (Matrix.noPivotLoop a state).singularStep = none := by
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, _h_step, _h_zero, _h_bound⟩
  · exact h_none
  · have h_persist :=
      noPivotLoop_singularStep a b state h_init h_sing
    rw [h_final] at h_persist
    nomatch h_persist

/-- If the full run records its first singular step after `a`, then the prefix
of length `a` is non-singular. -/
private theorem noPivotLoop_prefix_none_of_final_singular_after
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none) {s : Nat}
    (h_final : (Matrix.noPivotLoop (a + b) state).singularStep = some s)
    (hs_after : state.step + a ≤ s) :
    (Matrix.noPivotLoop a state).singularStep = none := by
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, _h_step, _h_zero, _h_bound⟩
  · exact h_none
  · have h_persist :=
      noPivotLoop_singularStep a b state h_init h_sing
    rw [h_final] at h_persist
    injection h_persist with hks
    have hk_lt : k.val < state.step + a :=
      noPivotLoop_singularStep_lt a state h_init k.val h_sing
    omega

/-- No-pivot Bareiss projection at the `gramDetVecEntry` diagonal slot:
running `Matrix.noPivotLoop r` from the initial state on the full Gram
matrix and on its `(r+1)`-leading prefix yields states whose `(r, r)`
diagonal entry agrees (after the leading-prefix identification) and
whose `singularStep` field agrees. This is the executable-loop
projection needed by the parent assembly of
`gramDetVecEntry_eq_leadingPrefix_bareiss`. -/
private theorem noPivotLoop_full_eq
    (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    let GM := Matrix.gramMatrix b
    let hK : r + 1 ≤ n := Nat.succ_le_of_lt hr
    let LP := Matrix.leadingPrefix GM (r + 1) hK
    let s_full := Matrix.noPivotLoop r (Matrix.noPivotInitialState GM)
    let s_pref := Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)
    s_full.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        s_pref.matrix[(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))]
      ∧ s_full.singularStep = s_pref.singularStep := by
  intro GM hK LP s_full s_pref
  have h_sync := noPivotLoop_sync_leadingPrefix_aux hK r
    (Matrix.noPivotInitialState GM) (Matrix.noPivotInitialState LP)
    rfl rfl rfl rfl rfl
    (show r + (Matrix.noPivotInitialState GM).step < r + 1 by
      simp [Matrix.noPivotInitialState])
  obtain ⟨_, _, _, h_sing, h_mat⟩ := h_sync
  refine ⟨?_, h_sing⟩
  -- Diagonal: the (r, r) entry of s_full agrees with the (r, r) entry of s_pref via the
  -- leading-prefix identification.
  have hcongr := congrArg
    (fun (M : Matrix Int (r + 1) (r + 1)) =>
      M[(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))])
    h_mat
  simp only [Matrix.leadingPrefix_entry] at hcongr
  -- hcongr's LHS index in Fin n has val = r; same as the goal's LHS index.
  exact hcongr

/-- Signed diagonal projection for a non-singular target prefix: the final
no-pivot full-Gram diagonal at `r` is the public Bareiss determinant of the
`(r + 1)` leading prefix. -/
theorem bareissNoPivotData_diag_eq_leadingPrefix_bareiss_of_prefix_nonsingular
    (b : Matrix Int n m) (r : Nat) (hr : r < n)
    (h_nonsing :
      (Matrix.noPivotLoop r
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[
        (⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
      Matrix.bareiss
        (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
          (Nat.succ_le_of_lt hr)) := by
  let GM := Matrix.gramMatrix b
  let init := Matrix.noPivotInitialState GM
  let fullAtR := Matrix.noPivotLoop r init
  let LP := Matrix.leadingPrefix GM (r + 1) (Nat.succ_le_of_lt hr)
  have h_step_r : fullAtR.step = r := by
    have h_room : init.step + r + 1 ≤ n := by
      simp [init, Matrix.noPivotInitialState]
      omega
    have h := noPivotLoop_step_eq_add_of_singularStep_none r init rfl h_room h_nonsing
    simpa [fullAtR, init, Matrix.noPivotInitialState] using h
  have h_factor :
      Matrix.noPivotLoop n init = Matrix.noPivotLoop (n - r) fullAtR := by
    have h_add := noPivotLoop_add r (n - r) init
    have h_split : r + (n - r) = n := by omega
    simpa [fullAtR, h_split] using h_add
  have h_final_diag :
      (Matrix.noPivotLoop n init).matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        fullAtR.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] := by
    rw [h_factor]
    have h_le : (⟨r, hr⟩ : Fin n).val ≤ fullAtR.step := by
      change r ≤ fullAtR.step
      rw [h_step_r]
      exact Nat.le_refl r
    exact Matrix.noPivotLoop_diag_of_le_step (n - r) fullAtR (⟨r, hr⟩ : Fin n) h_le
  obtain ⟨h_diag, h_sing⟩ :=
    noPivotLoop_full_eq (b := b) r hr
  have h_pref_nonsing :
      (Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)).singularStep = none := by
    rw [← h_sing]
    exact h_nonsing
  have h_bareiss :=
    Matrix.bareiss_eq_noPivotLoop_last_of_no_singular (M := LP) h_pref_nonsing
  calc
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[
        (⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        fullAtR.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] := by
          simpa [Matrix.bareissNoPivotData, Matrix.finish, GM, init, fullAtR] using
            h_final_diag
    _ =
        (Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)).matrix[
          (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][
          (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))] := by
          simpa [GM, LP, fullAtR, init] using h_diag
    _ = Matrix.bareiss LP := by
          simpa [LP, Fin.last] using h_bareiss.symm

end GramSchmidt.Int

end Hex
