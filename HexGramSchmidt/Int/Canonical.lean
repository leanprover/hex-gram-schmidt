module

public import HexGramSchmidt.Int.Core
import all HexGramSchmidt.Int.Core

public section

namespace Hex
namespace GramSchmidt.Int
/-! ### Gram row-span invariant for no-pivot Bareiss -/

/-- Row-vector interpretation of the trailing block during a no-pivot Bareiss
pass over a Gram matrix.  Each active trailing row carries an explicit integer
coefficient vector `coeff i` such that the represented row is
`Matrix.rowCombination b (coeff i)`, supported at coordinates `≤ i.val`, and
each matrix entry in that trailing row is its inner product against the
corresponding original row. -/
structure BareissGramRowInvariant (b : Matrix Int n m)
    (state : Matrix.BareissState n) where
  coeff : Fin n → Vector Int n
  coeff_supp : ∀ i k : Fin n, state.step ≤ i.val → i.val < k.val →
    (coeff i)[k] = 0
  entry_eq_dot : ∀ i j : Fin n, state.step ≤ i.val →
    state.matrix[i][j] =
      Matrix.dot (Matrix.rowCombination b (coeff i)) (b.row j)

/-- The initial no-pivot Gram state satisfies the row-coefficient invariant
with each row represented by the standard basis vector `eᵢ`. -/
@[expose]
def bareissGramRowInvariant_initial (b : Matrix Int n m) :
    BareissGramRowInvariant b
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := by
  refine
    { coeff := fun i => Vector.ofFn fun k : Fin n => if i = k then 1 else 0
      coeff_supp := ?_
      entry_eq_dot := ?_ }
  · intro i k _hi hik
    by_cases h : i = k
    · subst k
      omega
    · simp [h]
  · intro i j _hi
    have hsingle :
        Matrix.rowCombination b
            (Vector.ofFn fun k : Fin n => if i = k then (1 : Int) else 0) =
          b.row i :=
      Matrix.IsRREF.rowCombination_single (M := b) i
    rw [hsingle]
    simp [Matrix.noPivotInitialState, Matrix.gramMatrix, Matrix.ofFn, Matrix.dot]

/-- `foldl_sum_bareiss_row_update` pulls a Bareiss left row-update through a folded sum for later dot-product identities. -/
private theorem foldl_sum_bareiss_row_update
    {α : Type u} (xs : List α) (x y : Int) (u v w : α → Int)
    (accU accV : Int) :
    xs.foldl
        (fun acc a => acc + ((x * u a - y * v a) * w a))
        (x * accU - y * accV) =
      x * xs.foldl (fun acc a => acc + u a * w a) accU -
        y * xs.foldl (fun acc a => acc + v a * w a) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp
  | cons a xs ih =>
      simp only [List.foldl_cons]
      have hstep :
          x * accU - y * accV + ((x * u a - y * v a) * w a) =
            x * (accU + u a * w a) - y * (accV + v a * w a) := by
        grind
      rw [hstep]
      exact ih (accU + u a * w a) (accV + v a * w a)

/-- `dot_bareiss_row_update_left` expands the dot product of a Bareiss-updated left vector as the corresponding linear combination of dots. -/
private theorem dot_bareiss_row_update_left
    (x y : Int) (u v w : Vector Int m) :
    Matrix.dot (Vector.ofFn fun a : Fin m => x * u[a] - y * v[a]) w =
      x * Matrix.dot u w - y * Matrix.dot v w := by
  unfold Matrix.dot Hex.Vector.dotProduct
  simpa using
    foldl_sum_bareiss_row_update
      (xs := List.finRange m) x y
      (fun a : Fin m => u[a])
      (fun a : Fin m => v[a])
      (fun a : Fin m => w[a])
      0 0

/-- `foldl_sum_bareiss_row_update_right` pulls a Bareiss right row-update through a folded sum for the symmetric dot-product identity. -/
private theorem foldl_sum_bareiss_row_update_right
    {α : Type u} (xs : List α) (x y : Int) (u v w : α → Int)
    (accU accV : Int) :
    xs.foldl
        (fun acc a => acc + (w a * (x * u a - y * v a)))
        (x * accU - y * accV) =
      x * xs.foldl (fun acc a => acc + w a * u a) accU -
        y * xs.foldl (fun acc a => acc + w a * v a) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp
  | cons a xs ih =>
      simp only [List.foldl_cons]
      have hstep :
          x * accU - y * accV + (w a * (x * u a - y * v a)) =
            x * (accU + w a * u a) - y * (accV + w a * v a) := by
        grind
      rw [hstep]
      exact ih (accU + w a * u a) (accV + w a * v a)

/-- `dot_bareiss_row_update_right` expands the dot product with a Bareiss-updated right vector as the corresponding linear combination of dots. -/
private theorem dot_bareiss_row_update_right
    (x y : Int) (w u v : Vector Int m) :
    Matrix.dot w (Vector.ofFn fun a : Fin m => x * u[a] - y * v[a]) =
      x * Matrix.dot w u - y * Matrix.dot w v := by
  unfold Matrix.dot Hex.Vector.dotProduct
  simpa using
    foldl_sum_bareiss_row_update_right
      (xs := List.finRange m) x y
      (fun a : Fin m => u[a])
      (fun a : Fin m => v[a])
      (fun a : Fin m => w[a])
      0 0

/-- `rowCombination_bareiss_coeff_update` shows that row combinations respect the Bareiss coefficient update used by the Gram-row invariant. -/
private theorem rowCombination_bareiss_coeff_update
    (M : Matrix Int n m) (x y : Int) (c d : Vector Int n) :
    Matrix.rowCombination M (Vector.ofFn fun a : Fin n => x * c[a] - y * d[a]) =
      Vector.ofFn fun j : Fin m =>
        x * (Matrix.rowCombination M c)[j] - y * (Matrix.rowCombination M d)[j] := by
  apply Vector.ext
  intro j hj
  let jf : Fin m := ⟨j, hj⟩
  show
      (Matrix.rowCombination M (Vector.ofFn fun a : Fin n => x * c[a] - y * d[a]))[jf] =
        (Vector.ofFn fun j : Fin m =>
          x * (Matrix.rowCombination M c)[j] - y * (Matrix.rowCombination M d)[j])[jf]
  unfold Matrix.rowCombination
  have h_rhs :
      (Vector.ofFn fun j : Fin m => x * (M.transpose * c)[j] - y * (M.transpose * d)[j])[jf] =
        x * (M.transpose * c)[jf] - y * (M.transpose * d)[jf] := by
    change (Vector.ofFn fun j : Fin m =>
      x * (M.transpose * c)[j] - y * (M.transpose * d)[j]).get jf =
        x * (M.transpose * c)[jf] - y * (M.transpose * d)[jf]
    rw [Vector.get_ofFn]
  rw [h_rhs]
  repeat rw [Matrix.mulVec_getElem]
  exact dot_bareiss_row_update_right x y ((Matrix.transpose M).row jf) c d

/-- `exactDiv_eq_of_eq_mul_right` recovers the right quotient when the exact-division numerator is a quotient times the nonzero denominator. -/
private theorem exactDiv_eq_of_eq_mul_right
    {num denom q : Int} (hdenom : denom ≠ 0) (hnum : num = q * denom) :
  Matrix.exactDiv num denom = q := by
  have hnum' : num = denom * q := by
    grind
  have hdvd : denom ∣ num := by
    refine ⟨q, ?_⟩
    exact hnum'
  rw [Matrix.exactDiv_eq_divExact hdvd, Int.divExact_eq_ediv hdvd]
  exact Int.ediv_eq_of_eq_mul_left hdenom hnum

/-- `vector_exactDiv_eq_of_eq_mul_right` applies exact-division quotient recovery pointwise to coefficient vectors. -/
private theorem vector_exactDiv_eq_of_eq_mul_right
    {denom : Int} (hdenom : denom ≠ 0) (num q : Fin n → Int)
    (hnum : ∀ a : Fin n, num a = q a * denom) :
    (Vector.ofFn fun a : Fin n => Matrix.exactDiv (num a) denom) =
      Vector.ofFn q := by
  apply Vector.ext
  intro a ha
  let af : Fin n := ⟨a, ha⟩
  simp [exactDiv_eq_of_eq_mul_right hdenom (hnum af), af]

/-- `rowCombination_exactDiv_eq_of_eq_mul_right` replaces exact-divided coefficients by their quotient vector inside a row combination. -/
private theorem rowCombination_exactDiv_eq_of_eq_mul_right
    (M : Matrix Int n m) {denom : Int} (hdenom : denom ≠ 0)
    (num q : Fin n → Int) (hnum : ∀ a : Fin n, num a = q a * denom) :
    Matrix.rowCombination M (Vector.ofFn fun a : Fin n => Matrix.exactDiv (num a) denom) =
      Matrix.rowCombination M (Vector.ofFn q) := by
  rw [vector_exactDiv_eq_of_eq_mul_right hdenom num q hnum]

/-- `dot_rowCombination_exactDiv_eq_of_eq_mul_right` carries exact-division quotient recovery through a row combination and final dot product. -/
private theorem dot_rowCombination_exactDiv_eq_of_eq_mul_right
    (M : Matrix Int n m) {denom : Int} (hdenom : denom ≠ 0)
    (num q : Fin n → Int) (hnum : ∀ a : Fin n, num a = q a * denom)
    (w : Vector Int m) :
    Matrix.dot
        (Matrix.rowCombination M
          (Vector.ofFn fun a : Fin n => Matrix.exactDiv (num a) denom))
        w =
      Matrix.dot (Matrix.rowCombination M (Vector.ofFn q)) w := by
  rw [rowCombination_exactDiv_eq_of_eq_mul_right M hdenom num q hnum]

/-- Project the explicit coefficient witness for the row at index `i`. -/
private def bareissGramRowInvariantCoeff
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state) (i : Fin n) : Vector Int n :=
  hinv.coeff i

/-- `bareissGramRowInvariantCoeff_support` exposes the support vanishing condition for the projected Gram-row coefficient witness. -/
private theorem bareissGramRowInvariantCoeff_support
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state) (i : Fin n)
    (hi : state.step ≤ i.val) :
    ∀ k : Fin n, i.val < k.val →
      (bareissGramRowInvariantCoeff hinv i)[k] = 0 :=
  fun k hik => hinv.coeff_supp i k hi hik

/-- `bareissGramRowInvariantCoeff_row` identifies the projected Gram-row coefficient witness with the invariant's stored coefficient row. -/
private theorem bareissGramRowInvariantCoeff_row
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state) (i : Fin n) :
    Matrix.rowCombination b (bareissGramRowInvariantCoeff hinv i) =
      Matrix.rowCombination b (hinv.coeff i) := rfl

/-- Coefficient witness produced by one regular Bareiss step on the row at
index `i`.  The functional shape mirrors the row update on the matrix side. -/
@[expose]
def bareissGramRowInvariantStepCoeff
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state)
    (hnext : state.step + 1 < n) (i : Fin n) (_hi : state.step + 1 ≤ i.val) :
    Vector Int n :=
  let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
  Vector.ofFn fun a : Fin n =>
    Matrix.exactDiv
      (state.matrix[k][k] * (hinv.coeff i)[a] -
        state.matrix[i][k] * (hinv.coeff k)[a])
      state.prevPivot

/-- Coefficient-level exact-division provenance for one regular Gram-row
Bareiss step.  The quotient vector is kept separate from
`bareissGramRowInvariantStepCoeff` so later row-entry proofs can consume the
integer divisibility witness before projecting back to the existing exact-div
coefficient API. -/
structure BareissGramRegularStepQuotient
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state)
    (hnext : state.step + 1 < n) (i : Fin n) (_hi : state.step + 1 ≤ i.val) where
  q : Fin n → Int
  coeff_num_eq_mul :
    let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
    ∀ a : Fin n,
      state.matrix[k][k] * (hinv.coeff i)[a] -
        state.matrix[i][k] * (hinv.coeff k)[a] =
          q a * state.prevPivot

private theorem bareissGramRegularStepQuotient_stepCoeff_get
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) (a : Fin n) :
    (bareissGramRowInvariantStepCoeff hinv hnext i hi)[a] = hq.q a := by
  dsimp [bareissGramRowInvariantStepCoeff]
  rw [Vector.getElem_ofFn]
  exact exactDiv_eq_of_eq_mul_right hprev (hq.coeff_num_eq_mul a)

private theorem bareissGramRegularStepQuotient_stepCoeff_eq
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) :
    bareissGramRowInvariantStepCoeff hinv hnext i hi = Vector.ofFn hq.q := by
  apply Vector.ext
  intro a ha
  let af : Fin n := ⟨a, ha⟩
  simpa [af] using
    bareissGramRegularStepQuotient_stepCoeff_get
      (hinv := hinv) (hnext := hnext) (i := i) (hi := hi) hprev hq af

private theorem rowCombination_bareissGramRegularStepQuotient
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) :
    Matrix.rowCombination b (bareissGramRowInvariantStepCoeff hinv hnext i hi) =
      Matrix.rowCombination b (Vector.ofFn hq.q) := by
  rw [bareissGramRegularStepQuotient_stepCoeff_eq hprev hq]

theorem bareissGramRowInvariantStepCoeff_support
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state)
    (hnext : state.step + 1 < n) (i : Fin n) (hi : state.step + 1 ≤ i.val) :
    ∀ a : Fin n, i.val < a.val →
      (bareissGramRowInvariantStepCoeff hinv hnext i hi)[a] = 0 := by
  intro a hia
  dsimp [bareissGramRowInvariantStepCoeff]
  rw [Vector.getElem_ofFn]
  let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
  have h_i : state.step ≤ i.val := Nat.le_trans (Nat.le_succ state.step) hi
  have h_k : state.step ≤ k.val := Nat.le_refl _
  have hci : (hinv.coeff i)[a] = 0 := hinv.coeff_supp i a h_i hia
  have hk_lt_i : k.val < i.val := by
    dsimp [k]
    omega
  have hka : k.val < a.val := Nat.lt_trans hk_lt_i hia
  have hck : (hinv.coeff k)[a] = 0 := hinv.coeff_supp k a h_k hka
  have hciNat : (hinv.coeff i)[a.val] = 0 := by simpa using hci
  have hckNat :
      (hinv.coeff
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩ : Fin n))[a.val] = 0 := by
    simpa [k] using hck
  simp [hciNat, hckNat, Matrix.exactDiv]

/-! ### Canonical coefficient vector and canonicity predicate -/

/-- Canonical row-coefficient vector for the initial no-pivot Gram trajectory.

Base case: each row carries the standard basis vector `e_i`. Inductive step
(regular branch, active row): apply the fraction-free Bareiss row update via
`exactDiv`. Processed rows, singular branches, and done branches preserve the
previous vector unchanged — mirroring the row-invariant evolution in
`bareissGramRowInvariant_noPivotLoop_initialAux`.

Defined as a pure function of `b` and `fuel` (no `BareissGramRowInvariant`
argument), so the canonical coefficient is fixed by the matrix and step
count alone. Non-canonical row-coefficient witnesses are ruled out by the
`IsCanonicalAt` predicate consumed by `StepWitness`. -/
@[expose]
def bareissGramCanonicalCoeff (b : Matrix Int n m) :
    Nat → Fin n → Vector Int n
  | 0, i => Vector.ofFn fun k : Fin n => if i = k then 1 else 0
  | fuel + 1, i =>
    let state := Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))
    if hnext : state.step + 1 < n then
      if state.matrix[state.step][state.step] = 0 then
        bareissGramCanonicalCoeff b fuel i
      else if state.step + 1 ≤ i.val then
        let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
        Vector.ofFn fun a : Fin n =>
          Matrix.exactDiv
            (state.matrix[k][k] * (bareissGramCanonicalCoeff b fuel i)[a] -
              state.matrix[i][k] * (bareissGramCanonicalCoeff b fuel k)[a])
            state.prevPivot
      else
        bareissGramCanonicalCoeff b fuel i
    else
      bareissGramCanonicalCoeff b fuel i

/-- The canonical coefficient at `fuel = 0` is the standard basis vector. -/
@[simp, grind =] theorem bareissGramCanonicalCoeff_zero
    (b : Matrix Int n m) (i : Fin n) :
    bareissGramCanonicalCoeff b 0 i =
      Vector.ofFn fun k : Fin n => if i = k then (1 : Int) else 0 := rfl

/-- Recursion equation: regular-branch active-row case. With the branch
hypotheses in context, `simp [*]`/`simp_all` rewrites `bareissGramCanonicalCoeff`
at `fuel + 1` to its explicit Bareiss exact-division update. -/
@[simp, grind =] theorem bareissGramCanonicalCoeff_succ_regular
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) :
    bareissGramCanonicalCoeff b (fuel + 1) i =
      (let state := Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))
       let k : Fin n :=
         ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
       Vector.ofFn fun a : Fin n =>
         Matrix.exactDiv
           (state.matrix[k][k] * (bareissGramCanonicalCoeff b fuel i)[a] -
             state.matrix[i][k] * (bareissGramCanonicalCoeff b fuel k)[a])
           state.prevPivot) := by
  simp only [bareissGramCanonicalCoeff, dif_pos hnext, if_neg hp, if_pos hi]

/-- Recursion equation: regular-branch processed-row case. An already-processed
row (`i ≤ step`) keeps its previous coefficient vector, so the canonical
coefficient at `fuel + 1` collapses to the one at `fuel`. -/
@[simp, grind =] theorem bareissGramCanonicalCoeff_succ_processed
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (hi : ¬ (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) :
    bareissGramCanonicalCoeff b (fuel + 1) i =
      bareissGramCanonicalCoeff b fuel i := by
  simp only [bareissGramCanonicalCoeff, dif_pos hnext, if_neg hp, if_neg hi]

/-- Recursion equation: singular branch (zero diagonal). A zero pivot skips the
update, so the canonical coefficient at `fuel + 1` collapses to the one at
`fuel`. -/
@[simp, grind =] theorem bareissGramCanonicalCoeff_succ_singular
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] = 0) :
    bareissGramCanonicalCoeff b (fuel + 1) i =
      bareissGramCanonicalCoeff b fuel i := by
  simp only [bareissGramCanonicalCoeff, dif_pos hnext, if_pos hp]

/-- Recursion equation: done branch (no further work possible). Once the loop can
take no further step (`¬ step + 1 < n`), the canonical coefficient at `fuel + 1`
collapses to the one at `fuel`. -/
@[simp, grind =] theorem bareissGramCanonicalCoeff_succ_done
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n)
    (hDone : ¬ (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n) :
    bareissGramCanonicalCoeff b (fuel + 1) i =
      bareissGramCanonicalCoeff b fuel i := by
  simp only [bareissGramCanonicalCoeff, dif_neg hDone]

/-- A `BareissGramRowInvariant` on `noPivotLoop fuel (noPivotInitialState …)`
is *canonical at `fuel`* when every row's coefficient vector matches
`bareissGramCanonicalCoeff`. This is the soundness gate consumed by
`StepWitness`: non-canonical witnesses (which can shift coefficients by a
kernel vector while keeping `entry_eq_dot` satisfied) cannot invoke the
witness's quotient identity.

The SPEC counterexample at rows `(1,1), (1,0), (-1,-1)` (#6505) produces two
distinct `BareissGramRowInvariant` instances at the same loop state whose
coefficient vectors differ by the kernel vector. Both satisfy `entry_eq_dot`,
but only one (the canonical one) yields an integer Bareiss-step quotient. -/
@[expose]
def IsCanonicalAt (b : Matrix Int n m) (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)))) : Prop :=
  ∀ i : Fin n, hinv.coeff i = bareissGramCanonicalCoeff b fuel i

/-- The base-case row invariant at `fuel = 0` carries the standard basis vectors
and is therefore canonical. -/
theorem isCanonicalAt_initial (b : Matrix Int n m) :
    IsCanonicalAt b 0 (bareissGramRowInvariant_initial b) := by
  intro i
  rfl

/-- Transport along an equation of `BareissState`s preserves the `coeff` field
of a `BareissGramRowInvariant`. The field's type `Fin n → Vector Int n` does
not depend on the state index, so transport is the identity at that
projection. Used to discharge canonicity proofs after transporting an explicit
intermediate state back to the `noPivotLoop fuel initial` form. -/
theorem bareissGramRowInvariant_coeff_transport
    {b : Matrix Int n m} {st1 st2 : Matrix.BareissState n}
    (h : st1 = st2) (x : BareissGramRowInvariant b st2) (i : Fin n) :
    (h ▸ x).coeff i = x.coeff i := by
  cases h
  rfl

/-- Right-scalar linearity of the dot product against a `rowCombination` whose
coefficient vector is multiplied pointwise by a constant on the right.  Used
to factor the Bareiss exact-division denominator out of a quotient-backed row
combination. -/
private theorem dot_rowCombination_mul_right_int
    (b : Matrix Int n m) (f : Fin n → Int) (s : Int) (w : Vector Int m) :
    Matrix.dot
        (Matrix.rowCombination b (Vector.ofFn fun a : Fin n => f a * s)) w =
      Matrix.dot (Matrix.rowCombination b (Vector.ofFn f)) w * s := by
  have h_eq_input :
      (Vector.ofFn fun a : Fin n => f a * s) =
        Vector.ofFn fun a : Fin n =>
          s * (Vector.ofFn f)[a] - 0 * (Vector.ofFn f)[a] := by
    apply Vector.ext
    intro a ha
    simp only [Vector.getElem_ofFn]
    grind
  rw [h_eq_input]
  rw [rowCombination_bareiss_coeff_update b s 0 (Vector.ofFn f) (Vector.ofFn f)]
  rw [dot_bareiss_row_update_left s 0
    (Matrix.rowCombination b (Vector.ofFn f))
    (Matrix.rowCombination b (Vector.ofFn f)) w]
  grind

/-- Row-entry algebra for one regular Gram-row Bareiss step.  Consuming the
quotient-coefficient package `BareissGramRegularStepQuotient` together with a
nonzero `prevPivot` and the already-processed-column zero entries gives the
exact row-entry relation for `Matrix.stepMatrix` at row `i` and any column
`j`.  Covers the three column regimes: `j.val < state.step` (already-cleared
column, both sides zero), `j.val = state.step` (pivot column below the pivot,
both sides zero), and `state.step < j.val` (trailing block, `exactDiv` of the
Bareiss numerator). -/
private theorem bareissGramRegularStep_entry_eq_dot
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi)
    (h_processed : ∀ i' : Fin n, state.step ≤ i'.val →
      ∀ j' : Fin n, j'.val < state.step → state.matrix[i'][j'] = 0)
    (j : Fin n) :
    (Matrix.stepMatrix state.matrix state.step
        state.matrix[state.step][state.step] state.prevPivot)[i][j] =
      Matrix.dot
        (Matrix.rowCombination b
          (bareissGramRowInvariantStepCoeff hinv hnext i hi))
        (b.row j) := by
  let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
  have hk_val : k.val = state.step := rfl
  have h_step_le_i : state.step ≤ i.val := Nat.le_trans (Nat.le_succ _) hi
  have h_step_lt_i : state.step < i.val := hi
  have h_step_le_k : state.step ≤ k.val := Nat.le_refl _
  let lhsNum : Int :=
    state.matrix[k][k] * state.matrix[i][j] - state.matrix[i][k] * state.matrix[k][j]
  have hLHS_num : lhsNum =
      state.matrix[k][k] * state.matrix[i][j] -
        state.matrix[i][k] * state.matrix[k][j] := rfl
  -- Claim A: the dot product of the "numerator-side" row combination is lhsNum.
  have h_dot_num :
      Matrix.dot
          (Matrix.rowCombination b
            (Vector.ofFn fun a : Fin n =>
              state.matrix[k][k] * (hinv.coeff i)[a] -
                state.matrix[i][k] * (hinv.coeff k)[a]))
          (b.row j) = lhsNum := by
    rw [rowCombination_bareiss_coeff_update b
      state.matrix[k][k] state.matrix[i][k] (hinv.coeff i) (hinv.coeff k)]
    rw [dot_bareiss_row_update_left
      state.matrix[k][k] state.matrix[i][k]
      (Matrix.rowCombination b (hinv.coeff i))
      (Matrix.rowCombination b (hinv.coeff k))
      (b.row j)]
    rw [← hinv.entry_eq_dot i j h_step_le_i,
        ← hinv.entry_eq_dot k j h_step_le_k]
  -- Claim B: the dot product of the step coefficient row combination equals
  -- `exactDiv lhsNum prevPivot`.
  have h_dot_step :
      Matrix.dot
          (Matrix.rowCombination b
            (bareissGramRowInvariantStepCoeff hinv hnext i hi))
          (b.row j) = Matrix.exactDiv lhsNum state.prevPivot := by
    rw [rowCombination_bareissGramRegularStepQuotient hprev hq]
    refine (exactDiv_eq_of_eq_mul_right hprev ?_).symm
    have h_dot_mul :=
      dot_rowCombination_mul_right_int b hq.q state.prevPivot (b.row j)
    rw [← h_dot_mul]
    have h_q_eq_num :
        (Vector.ofFn fun a : Fin n => hq.q a * state.prevPivot) =
          (Vector.ofFn fun a : Fin n =>
            state.matrix[k][k] * (hinv.coeff i)[a] -
              state.matrix[i][k] * (hinv.coeff k)[a]) := by
      apply Vector.ext
      intro a ha
      rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
      exact (hq.coeff_num_eq_mul ⟨a, ha⟩).symm
    rw [h_q_eq_num]
    exact h_dot_num.symm
  -- Case split on `j.val` against `state.step`.
  by_cases hjk : state.step < j.val
  · -- Trailing block: stepMatrix is the Bareiss exactDiv update.
    rw [Matrix.stepMatrix_update_eq state.matrix state.step
      state.matrix[state.step][state.step] state.prevPivot i j h_step_lt_i hjk]
    rw [h_dot_step]
    rfl
  · by_cases hjeq : j.val = state.step
    · -- Pivot column, below the pivot: stepMatrix entry is 0, and `lhsNum = 0`.
      rw [Matrix.stepMatrix_pivot_col_below state.matrix state.step
        state.matrix[state.step][state.step] state.prevPivot i j h_step_lt_i hjeq]
      rw [h_dot_step]
      have h_j_eq_k : j = k := Fin.ext (by rw [hjeq, hk_val])
      have h_lhs_num_zero : lhsNum = 0 := by
        rw [hLHS_num, h_j_eq_k]; grind
      rw [h_lhs_num_zero]
      symm
      exact exactDiv_eq_of_eq_mul_right hprev
        (by grind : (0 : Int) = 0 * state.prevPivot)
    · -- Already-processed column: stepMatrix carries over, both sides zero.
      have hj_lt : j.val < state.step :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_lt hjk) hjeq
      have h_not_trail : ¬ (state.step < i.val ∧ state.step < j.val) := by
        intro ⟨_, h2⟩; exact absurd h2 (Nat.not_lt_of_le (Nat.le_of_lt hj_lt))
      have h_not_col : ¬ (state.step < i.val ∧ j.val = state.step) := by
        intro ⟨_, h2⟩; exact hjeq h2
      rw [Matrix.stepMatrix_eq_of_not_update state.matrix state.step
        state.matrix[state.step][state.step] state.prevPivot i j h_not_trail h_not_col]
      have h_i_j_zero : state.matrix[i][j] = 0 := h_processed i h_step_le_i j hj_lt
      have h_k_j_zero : state.matrix[k][j] = 0 := h_processed k h_step_le_k j hj_lt
      have h_lhs_num_zero : lhsNum = 0 := by
        rw [hLHS_num, h_i_j_zero, h_k_j_zero]; grind
      rw [h_dot_step, h_lhs_num_zero, h_i_j_zero]
      symm
      exact exactDiv_eq_of_eq_mul_right hprev
        (by grind : (0 : Int) = 0 * state.prevPivot)

/-- One regular no-pivot Bareiss step preserves the Gram row-coefficient
invariant, provided the later loop proof supplies the exact-division entry
relation for the fraction-free updated row combinations. -/
@[expose]
def bareissGramRowInvariant_regular_step
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hnext : state.step + 1 < n)
    (_hp : state.matrix[state.step][state.step] ≠ 0)
    (hinv : BareissGramRowInvariant b state)
    (hentry :
      ∀ i j : Fin n, (hi : state.step + 1 ≤ i.val) →
        (Matrix.stepMatrix state.matrix state.step
            state.matrix[state.step][state.step] state.prevPivot)[i][j] =
          Matrix.dot
            (Matrix.rowCombination b
              (bareissGramRowInvariantStepCoeff hinv hnext i hi))
            (b.row j)) :
    BareissGramRowInvariant b
      { step := state.step + 1
        matrix := Matrix.stepMatrix state.matrix state.step
          state.matrix[state.step][state.step] state.prevPivot
        prevPivot := state.matrix[state.step][state.step]
        rowSwaps := state.rowSwaps
        singularStep := none } := by
  refine
    { coeff := fun i =>
        if hi : state.step + 1 ≤ i.val then
          bareissGramRowInvariantStepCoeff hinv hnext i hi
        else
          hinv.coeff i
      coeff_supp := ?_
      entry_eq_dot := ?_ }
  · intro i k hi hik
    have hi' : state.step + 1 ≤ i.val := hi
    simp [hi', bareissGramRowInvariantStepCoeff_support hinv hnext i hi' k hik]
  · intro i j hi
    have hi' : state.step + 1 ≤ i.val := hi
    simpa [hi'] using hentry i j hi'

/-- The coefficient vectors produced by `bareissGramRowInvariant_regular_step`
from a canonical input invariant match `bareissGramCanonicalCoeff` at the
next-step fuel index. Used to propagate canonicity through one regular Bareiss
step inside `bareissGramRowInvariant_noPivotLoop_initialAux`. -/
theorem bareissGramRowInvariant_regular_step_coeff_canonical
    (b : Matrix Int n m) (elapsed : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_canon : IsCanonicalAt b elapsed hinv)
    (hnext :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (hentry :
      ∀ i j : Fin n,
        (hi : (Matrix.noPivotLoop elapsed
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) →
        (Matrix.stepMatrix
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
              (Matrix.noPivotLoop elapsed
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
              (Matrix.noPivotLoop elapsed
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step]
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).prevPivot)[i][j] =
          Matrix.dot
            (Matrix.rowCombination b
              (bareissGramRowInvariantStepCoeff hinv hnext i hi))
            (b.row j))
    (i : Fin n) :
    (bareissGramRowInvariant_regular_step hnext hp hinv hentry).coeff i =
      bareissGramCanonicalCoeff b (elapsed + 1) i := by
  -- The regular_step constructor produces `if step+1 ≤ i.val then stepCoeff else hinv.coeff i`.
  by_cases hi : (Matrix.noPivotLoop elapsed
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val
  · have hLHS :
        (bareissGramRowInvariant_regular_step hnext hp hinv hentry).coeff i =
          bareissGramRowInvariantStepCoeff hinv hnext i hi := by
      show (if hi : _ then _ else _) = _
      rw [dif_pos hi]
    rw [hLHS]
    rw [bareissGramCanonicalCoeff_succ_regular b elapsed i hnext hp hi]
    show Vector.ofFn (fun a : Fin n =>
        Matrix.exactDiv
          (_ * (hinv.coeff i)[a] - _ * (hinv.coeff _)[a])
          _) = _
    rw [h_canon i,
        h_canon ⟨(Matrix.noPivotLoop elapsed
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step,
          Nat.lt_trans (Nat.lt_succ_self _) hnext⟩]
  · have hLHS :
        (bareissGramRowInvariant_regular_step hnext hp hinv hentry).coeff i =
          hinv.coeff i := by
      show (if hi : _ then _ else _) = _
      rw [dif_neg hi]
    rw [hLHS, bareissGramCanonicalCoeff_succ_processed b elapsed i hnext hp hi]
    exact h_canon i

/-- If the initial no-pivot Gram pass reaches column `s` without recording a
singular step, its state step is exactly `s`.  This keeps the later singular
pivot argument from unfolding the loop just to align the searched column. -/
private theorem noPivotLoop_initial_gram_step_eq
    (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.noPivotLoop s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step = s := by
  have h_room :
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + s + 1 ≤ n := by
    simp [Matrix.noPivotInitialState]
    omega
  have h_step :=
    Matrix.noPivotLoop_step_eq_add_of_singularStep_none s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_room h_prefix_none
  simpa [Matrix.noPivotInitialState] using h_step

/-- On a nonsingular initial no-pivot Gram trajectory, any current state that is
ready for a regular next step has a nonzero previous pivot. -/
private theorem noPivotLoop_initial_gram_prevPivot_ne_zero
    (b : Matrix Int n m) (fuel : Nat)
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (_hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (_hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0) :
    (Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).prevPivot ≠ 0 := by
  apply noPivotLoop_prevPivot_ne_zero
  · simp [Matrix.noPivotInitialState]
  · exact h_prefix_none

/-- Package a proved zero suffix in the current Gram pivot column into the
executable row-pivot search failure expected by `Matrix.pivotLoop`. -/
private theorem noPivotLoop_initial_gram_findPivot?_eq_none_of_column_zero
    (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (h_column_zero :
      ∀ i : Fin n, s + 1 ≤ i.val →
        (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0) :
    Matrix.findPivot?
        (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix
        (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n) (s + 1) = none := by
  have _h_step :=
    noPivotLoop_initial_gram_step_eq b s hs h_prefix_none
  exact Matrix.findPivot?_eq_none_of_zero _ _ _ h_column_zero

/-- After running `noPivotLoop fuel` from a state with `singularStep = none`, if
the result also has `singularStep = none`, then every column strictly between
the initial step and the final step is zero below the pivot in the final
matrix. Each such column was processed by a regular Bareiss step that cleared
its sub-diagonal entries, and no later iteration touches them. -/
private theorem noPivotLoop_matrix_processed_col_eq_zero {n : Nat} (fuel : Nat) :
    ∀ (state : Matrix.BareissState n),
      (Matrix.noPivotLoop fuel state).singularStep = none →
      ∀ (k : Nat), state.step ≤ k →
        k < (Matrix.noPivotLoop fuel state).step →
        ∀ (kFin : Fin n), kFin.val = k →
        ∀ (i : Fin n), k < i.val →
          (Matrix.noPivotLoop fuel state).matrix[i][kFin] = 0 := by
  induction fuel with
  | zero =>
      intros state _h_result k hk_ge hk_lt _kFin _hkFin i _hki
      simp [Matrix.noPivotLoop_zero_fuel] at hk_lt
      omega
  | succ f ih =>
      intros state h_result_none k hk_ge hk_lt kFin hkFin i hki
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · -- Singular branch contradicts h_result_none.
          rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_result_none
          simp at h_result_none
        · -- Regular branch.
          let next : Matrix.BareissState n :=
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          have h_eq_next : Matrix.noPivotLoop (f + 1) state =
              Matrix.noPivotLoop f next :=
            Matrix.noPivotLoop_regular_branch f state hDone hp
          rw [h_eq_next] at h_result_none hk_lt ⊢
          by_cases hk_eq : k = state.step
          · -- k just got processed: column k was zeroed by stepMatrix.
            have hi_lt : state.step < i.val := hk_eq ▸ hki
            have hkFin_eq : kFin.val = state.step := hk_eq ▸ hkFin
            have h_next_zero : next.matrix[i][kFin] = 0 :=
              Matrix.stepMatrix_pivot_col_below state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot i kFin hi_lt hkFin_eq
            have h_fixed : kFin.val < next.step := by
              change kFin.val < state.step + 1
              omega
            have h_eq :=
              Matrix.noPivotLoop_matrix_entry_of_row_le_or_col_lt f next i kFin
                (Or.inr h_fixed)
            rw [h_eq]
            exact h_next_zero
          · -- k was processed at a later step inside `next`.
            have hk_ge_next : next.step ≤ k := by
              change state.step + 1 ≤ k
              omega
            exact ih next h_result_none k hk_ge_next hk_lt kFin hkFin i hki
      · -- Done branch: state.step unchanged, so hk_lt collapses.
        have h_eq_state : Matrix.noPivotLoop (f + 1) state = state :=
          Matrix.noPivotLoop_done f state hDone
        rw [h_eq_state] at h_result_none hk_lt ⊢
        omega

/-- Initial no-pivot Gram trajectory specialization of the regular row-entry
algebra.  The quotient package supplies the coefficient-side divisibility
provenance; the initial trajectory supplies nonzero `prevPivot` and the
already-processed column zeros needed by the one-step algebra. -/
private theorem bareissGramInitialRegularStep_entry_eq_dot
    (b : Matrix Int n m) (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (i j : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) :
    (Matrix.stepMatrix
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
            (Matrix.noPivotLoop fuel
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
            (Matrix.noPivotLoop fuel
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step]
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).prevPivot)[i][j] =
      Matrix.dot
        (Matrix.rowCombination b
          (bareissGramRowInvariantStepCoeff hinv hnext i hi))
        (b.row j) := by
  let state :=
    Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))
  have hprev : state.prevPivot ≠ 0 :=
    noPivotLoop_initial_gram_prevPivot_ne_zero
      b fuel h_prefix_none hnext hp
  have h_processed :
      ∀ i' : Fin n, state.step ≤ i'.val →
        ∀ j' : Fin n, j'.val < state.step → state.matrix[i'][j'] = 0 := by
    intro i' hi' j' hj'
    exact noPivotLoop_matrix_processed_col_eq_zero fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_prefix_none
      j'.val (by simp [Matrix.noPivotInitialState]) hj' j' rfl i'
      (Nat.lt_of_lt_of_le hj' hi')
  exact bareissGramRegularStep_entry_eq_dot hprev hq h_processed j

/-- Per-step quotient package for the initial no-pivot Gram trajectory,
restricted to *canonical* row-coefficient witnesses via `IsCanonicalAt`.

`StepWitness.Cell` is an alias for `BareissGramRegularStepQuotient` whose
canonicity gate (`h_canon`) prevents non-canonical `BareissGramRowInvariant`
witnesses — which can shift coefficients by a kernel vector while still
satisfying `entry_eq_dot` — from supplying integer quotients. The kernel-shift
counterexample (SPEC #6505: rows `(1,1), (1,0), (-1,-1)` at row 2 step 1)
shows the restriction is necessary: distinct non-canonical witnesses produce
numerators differing by `1`, which is not divisible by `prevPivot = 2`. -/
@[expose]
abbrev StepWitness.Cell
    (b : Matrix Int n m) (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (_h_canon : IsCanonicalAt b fuel hinv)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) :
    Type :=
  BareissGramRegularStepQuotient hinv hnext i hi

/-- Quotient provenance for the initial no-pivot Gram trajectory, restricted
to canonical `BareissGramRowInvariant` witnesses via `IsCanonicalAt`. The
provider supplies, at every reachable regular Bareiss step, an integer
quotient `q : Fin n → Int` realising the Bareiss-row-update divisibility on
the canonical coefficient vectors.

Concrete providers are constructed in `HexGramSchmidtMathlib`, where the
Bareiss-Desnanot proof infrastructure on PSD Gram minors is available; the
Mathlib-free layer only consumes this abstraction. -/
@[expose]
abbrev StepWitness (b : Matrix Int n m) : Type :=
  ∀ (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_canon : IsCanonicalAt b fuel hinv)
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (_hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val),
      StepWitness.Cell b fuel hinv h_canon hnext i hi

/-- Canonical row-coefficients are unchanged once the no-pivot Bareiss loop
has reached the boundary `state.step + 1 = n`. Used to propagate canonicity
through the done branch of `bareissGramRowInvariant_noPivotLoop_initialAux`. -/
private theorem bareissGramCanonicalCoeff_eq_of_done
    {n m : Nat} (b : Matrix Int n m) (elapsed j : Nat) (i : Fin n)
    (hDone :
      ¬ (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n) :
    bareissGramCanonicalCoeff b (elapsed + j) i =
      bareissGramCanonicalCoeff b elapsed i := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have h_state_eq :
          Matrix.noPivotLoop (elapsed + j)
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
          Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := by
        rw [noPivotLoop_add elapsed j]
        exact noPivotLoop_id_at_done j _ hDone
      have hDone' :
          ¬ (Matrix.noPivotLoop (elapsed + j)
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n := by
        rw [h_state_eq]; exact hDone
      rw [show elapsed + (j + 1) = (elapsed + j) + 1 from by omega,
          bareissGramCanonicalCoeff_succ_done b (elapsed + j) i hDone']
      exact ih

/-- State-equation variant of `bareissGramCanonicalCoeff_succ_singular`: when
the no-pivot Bareiss state at `fuel` is propositionally equal to some `s`, the
singular hypothesis on `s` propagates to the canonical-coefficient identity at
`fuel + 1`. Used by `bareissGramCanonicalCoeff_eq_of_singular` to apply the
succ-singular equation at the singular fixed-point without rewriting through
dependent matrix-access proofs. -/
private theorem bareissGramCanonicalCoeff_succ_singular_of_state_eq
    {n m : Nat} (b : Matrix Int n m) (fuel : Nat) (i : Fin n)
    {s : Matrix.BareissState n}
    (h_state : Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) = s)
    (hDone : s.step + 1 < n)
    (hp : s.matrix[s.step][s.step] = 0) :
    bareissGramCanonicalCoeff b (fuel + 1) i =
      bareissGramCanonicalCoeff b fuel i := by
  subst h_state
  exact bareissGramCanonicalCoeff_succ_singular b fuel i hDone hp

/-- Canonical row-coefficients are unchanged by extending the no-pivot Bareiss
loop past a singular step. Used to propagate canonicity through the singular
branch of `bareissGramRowInvariant_noPivotLoop_initialAux`. -/
private theorem bareissGramCanonicalCoeff_eq_of_singular
    {n m : Nat} (b : Matrix Int n m) (elapsed j : Nat) (i : Fin n)
    (hDone :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] = 0) :
    bareissGramCanonicalCoeff b (elapsed + 1 + j) i =
      bareissGramCanonicalCoeff b elapsed i := by
  induction j with
  | zero =>
      exact bareissGramCanonicalCoeff_succ_singular b elapsed i hDone hp
  | succ j ih =>
      have h_one :
          Matrix.noPivotLoop (elapsed + 1)
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
          { (Matrix.noPivotLoop elapsed
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))) with
            singularStep := some (Matrix.noPivotLoop elapsed
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step } := by
        rw [noPivotLoop_add elapsed 1]
        exact Matrix.noPivotLoop_singular_branch 0 _ hDone hp
      have h_state_eq :
          Matrix.noPivotLoop (elapsed + 1 + j)
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
          { (Matrix.noPivotLoop elapsed
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))) with
            singularStep := some (Matrix.noPivotLoop elapsed
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step } := by
        rw [noPivotLoop_add (elapsed + 1) j, h_one]
        exact noPivotLoop_id_at_singular_fixedpoint j _ hDone hp rfl
      rw [show elapsed + 1 + (j + 1) = (elapsed + 1 + j) + 1 from by omega,
          bareissGramCanonicalCoeff_succ_singular_of_state_eq
            b (elapsed + 1 + j) i h_state_eq hDone hp]
      exact ih

/-- Initial no-pivot Gram specialization indexed by elapsed fuel.  The regular
branch no longer asks callers for a row-entry equation; it obtains the
reachable row-entry relation from `bareissGramInitialRegularStep_entry_eq_dot`
using the supplied quotient provenance.

Threads `IsCanonicalAt` through the recursion so that the canonicity gate of
`StepWitness` can be discharged at every regular step. The return type packages
the row invariant together with the proof that its coefficients match
`bareissGramCanonicalCoeff` at the elapsed-plus-fuel index. -/
private def bareissGramRowInvariant_noPivotLoop_initialAux
    (b : Matrix Int n m) (elapsed fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_canon : IsCanonicalAt b elapsed hinv)
    (h_prefix_none :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hquot : StepWitness b) :
    { hinv' : BareissGramRowInvariant b
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotLoop elapsed
            (Matrix.noPivotInitialState (Matrix.gramMatrix b)))) //
      ∀ i : Fin n,
        hinv'.coeff i = bareissGramCanonicalCoeff b (elapsed + fuel) i } := by
  induction fuel generalizing elapsed with
  | zero =>
      exact ⟨hinv, h_canon⟩
  | succ fuel ih =>
      let state :=
        Matrix.noPivotLoop elapsed
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch fuel state hDone hp]
          refine ⟨{ coeff := hinv.coeff
                    coeff_supp := ?_
                    entry_eq_dot := ?_ }, ?_⟩
          · simpa using hinv.coeff_supp
          · simpa using hinv.entry_eq_dot
          · intro i
            show hinv.coeff i = bareissGramCanonicalCoeff b (elapsed + (fuel + 1)) i
            rw [h_canon i,
                show elapsed + (fuel + 1) = elapsed + 1 + fuel from by omega]
            exact (bareissGramCanonicalCoeff_eq_of_singular
              b elapsed fuel i hDone hp).symm
        · rw [Matrix.noPivotLoop_regular_branch fuel state hDone hp]
          have hstep :
              Matrix.noPivotLoop (elapsed + 1)
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
                ({ step := state.step + 1
                   matrix := Matrix.stepMatrix state.matrix state.step
                     state.matrix[state.step][state.step] state.prevPivot
                   prevPivot := state.matrix[state.step][state.step]
                   rowSwaps := state.rowSwaps
                   singularStep := none } : Matrix.BareissState n) := by
            rw [noPivotLoop_add elapsed 1
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))]
            rw [Matrix.noPivotLoop_regular_branch 0 state hDone hp]
            simp [Matrix.noPivotLoop_zero_fuel]
          have hentry := fun i j hi =>
            bareissGramInitialRegularStep_entry_eq_dot
              (b := b) elapsed hinv h_prefix_none hDone hp i j hi
              (hquot elapsed hinv h_canon h_prefix_none hDone hp i hi)
          let hinv_next := bareissGramRowInvariant_regular_step hDone hp hinv hentry
          have h_canon_next_pre :
              ∀ i : Fin n,
                hinv_next.coeff i = bareissGramCanonicalCoeff b (elapsed + 1) i := fun i =>
            bareissGramRowInvariant_regular_step_coeff_canonical
              b elapsed hinv h_canon hDone hp hentry i
          rw [← hstep]
          have h_canon_next :
              IsCanonicalAt b (elapsed + 1) (hstep ▸ hinv_next) := by
            intro i
            show (hstep ▸ hinv_next).coeff i = bareissGramCanonicalCoeff b (elapsed + 1) i
            rw [bareissGramRowInvariant_coeff_transport hstep hinv_next i]
            exact h_canon_next_pre i
          have h_prefix_next :
              (Matrix.noPivotLoop (elapsed + 1)
                (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
            rw [hstep]
          let ih_result :=
            ih (elapsed := elapsed + 1) (hstep ▸ hinv_next) h_canon_next h_prefix_next
          refine ⟨ih_result.1, ?_⟩
          intro i
          rw [show elapsed + (fuel + 1) = (elapsed + 1) + fuel from by omega]
          exact ih_result.2 i
      · rw [Matrix.noPivotLoop_done fuel state hDone]
        refine ⟨hinv, ?_⟩
        intro i
        rw [h_canon i]
        exact (bareissGramCanonicalCoeff_eq_of_done b elapsed (fuel + 1) i hDone).symm

/-- Initial-state specialization of the row invariant for the no-pivot pass
over a Gram matrix.  Callers supply only quotient provenance for reachable
regular branches; the row-entry equation is derived internally. -/
private def bareissGramRowInvariant_noPivotLoop_initial
    (b : Matrix Int n m) (fuel : Nat)
    (hquot : StepWitness b) :
    BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState (Matrix.gramMatrix b))) :=
  (bareissGramRowInvariant_noPivotLoop_initialAux
    (b := b) 0 fuel (bareissGramRowInvariant_initial b)
    (isCanonicalAt_initial b) rfl hquot).1

/-- The produced row invariant from the initial no-pivot Gram trajectory is
canonical: its coefficients match `bareissGramCanonicalCoeff` at every fuel
index. This is the canonicity gate consumed by `StepWitness.Cell`. -/
private theorem bareissGramRowInvariant_noPivotLoop_initial_canonical
    (b : Matrix Int n m) (fuel : Nat) (hquot : StepWitness b) :
    IsCanonicalAt b fuel
      (bareissGramRowInvariant_noPivotLoop_initial b fuel hquot) := by
  intro i
  simpa using (bareissGramRowInvariant_noPivotLoop_initialAux
    (b := b) 0 fuel (bareissGramRowInvariant_initial b)
    (isCanonicalAt_initial b) rfl hquot).2 i

/-- Matrix-level Bareiss-step divisibility on the initial no-pivot Gram
trajectory: the numerator of one fraction-free row update is divisible by the
previous pivot. The witness comes from the canonical-`StepWitness` quotient
package applied at the reachable regular step, with the matrix-level numerator
recovered by taking the dot product of the coefficient-level identity against
the input row `b.row j`. -/
private theorem noPivotLoop_initial_gram_bareiss_step_dvd
    (b : Matrix Int n m) (hquot : StepWitness b)
    (fuel : Nat)
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (i j : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) :
    let state := Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))
    let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
    state.prevPivot ∣
      state.matrix[k][k] * state.matrix[i][j] -
        state.matrix[i][k] * state.matrix[k][j] := by
  intro state k
  let hinv := bareissGramRowInvariant_noPivotLoop_initial b fuel hquot
  let h_canon := bareissGramRowInvariant_noPivotLoop_initial_canonical b fuel hquot
  have hq := hquot fuel hinv h_canon h_prefix_none hnext hp i hi
  have h_step_le_i : state.step ≤ i.val := Nat.le_trans (Nat.le_succ _) hi
  have h_step_le_k : state.step ≤ k.val := Nat.le_refl _
  refine ⟨Matrix.dot (Matrix.rowCombination b (Vector.ofFn hq.q)) (b.row j), ?_⟩
  rw [hinv.entry_eq_dot i j h_step_le_i, hinv.entry_eq_dot k j h_step_le_k]
  rw [← dot_bareiss_row_update_left state.matrix[k][k] state.matrix[i][k]
        (Matrix.rowCombination b (hinv.coeff i))
        (Matrix.rowCombination b (hinv.coeff k))
        (b.row j)]
  rw [← rowCombination_bareiss_coeff_update b
        state.matrix[k][k] state.matrix[i][k] (hinv.coeff i) (hinv.coeff k)]
  have h_q_eq_num :
      (Vector.ofFn fun a : Fin n =>
        state.matrix[k][k] * (hinv.coeff i)[a] -
          state.matrix[i][k] * (hinv.coeff k)[a]) =
        Vector.ofFn fun a : Fin n => hq.q a * state.prevPivot := by
    apply Vector.ext
    intro a ha
    rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
    exact hq.coeff_num_eq_mul ⟨a, ha⟩
  rw [h_q_eq_num]
  rw [dot_rowCombination_mul_right_int b hq.q state.prevPivot (b.row j)]
  exact Int.mul_comm _ _

/-- Row-vector consumer for an initial no-pivot Gram pass.  A single supported
integer row combination represents the active row `i` against every original
input row, so downstream singular-column arguments do not need to inspect
`BareissGramRowInvariant` or supply the generic regular-branch row-entry
equation. -/
private theorem noPivotLoop_initial_gram_exists_rowVec
    (b : Matrix Int n m) (fuel : Nat)
    (hquot : StepWitness b)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ i.val) :
    ∃ v : Vector Int m,
      (∃ c : Vector Int n,
        (∀ k : Fin n, i.val < k.val → c[k] = 0) ∧
          v = Matrix.rowCombination b c) ∧
        ∀ j : Fin n,
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] =
            Matrix.dot v (b.row j) := by
  let hinv :=
    bareissGramRowInvariant_noPivotLoop_initial b fuel hquot
  refine ⟨Matrix.rowCombination b (hinv.coeff i), ?_, ?_⟩
  · exact ⟨hinv.coeff i, fun k hik => hinv.coeff_supp i k hi hik, rfl⟩
  · intro j
    exact hinv.entry_eq_dot i j hi

/-- `int_mul_self_nonneg`: the square `x * x` of an integer is nonnegative,
the base nonnegativity fact for the integer-vector self-dot bounds below. -/
private theorem int_mul_self_nonneg (x : Int) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using
    (Lean.Grind.OrderedRing.sq_nonneg (a := x))

/-- `int_mul_self_eq_zero_of_nonpos`: an integer whose square is nonpositive is
zero, the per-component step turning a vanishing self-dot into a zero entry. -/
private theorem int_mul_self_eq_zero_of_nonpos (x : Int) (h : x * x ≤ 0) : x = 0 := by
  have hnonneg : 0 ≤ x * x := int_mul_self_nonneg x
  have hsquare : x * x = 0 := Int.le_antisymm h hnonneg
  rcases Int.mul_eq_zero.mp hsquare with h0 | h0 <;> exact h0

/-- `foldl_int_dot_self_start_le`: the running self-dot fold over `xs` never
drops below its nonnegative starting accumulator, since each added square is
nonnegative; the monotonicity used to pin the accumulator at zero. -/
private theorem foldl_int_dot_self_start_le (xs : List (Fin m)) (v : Vector Int m)
    (acc : Int) (hacc : 0 ≤ acc) :
    acc ≤ xs.foldl (fun sum i => sum + v[i] * v[i]) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hsq : 0 ≤ v[i] * v[i] := int_mul_self_nonneg v[i]
      have hnext : 0 ≤ acc + v[i] * v[i] := by grind
      exact Int.le_trans (by grind) (ih (acc := acc + v[i] * v[i]) hnext)

/-- `foldl_int_dot_self_eq_zero_of_mem`: if the self-dot fold over `xs` from a
nonnegative accumulator vanishes, then every entry indexed by `xs` is zero,
the per-index extraction behind finite-dimensional positive-definiteness. -/
private theorem foldl_int_dot_self_eq_zero_of_mem (xs : List (Fin m))
    (v : Vector Int m) (acc : Int) (hacc : 0 ≤ acc)
    (hzero : xs.foldl (fun sum i => sum + v[i] * v[i]) acc = 0) :
    ∀ i ∈ xs, v[i] = 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons head rest ih =>
      intro i hi
      simp only [List.mem_cons] at hi
      have hsq : 0 ≤ v[head] * v[head] := int_mul_self_nonneg v[head]
      have hnext_nonneg : 0 ≤ acc + v[head] * v[head] := by grind
      have hnext_le_zero : acc + v[head] * v[head] ≤ 0 := by
        have hle :=
          foldl_int_dot_self_start_le (xs := rest) (v := v)
            (acc := acc + v[head] * v[head]) hnext_nonneg
        have hzero' :
            rest.foldl (fun sum i => sum + v[i] * v[i])
              (acc + v[head] * v[head]) = 0 := by
          simpa using hzero
        rw [hzero'] at hle
        exact hle
      have hnext_zero : acc + v[head] * v[head] = 0 := by grind
      have hhead_zero : v[head] = 0 := by
        apply int_mul_self_eq_zero_of_nonpos
        grind
      cases hi with
      | inl h =>
          subst i
          exact hhead_zero
      | inr h =>
          exact ih (acc := acc + v[head] * v[head]) hnext_nonneg hzero i h

/-- `int_dot_self_eq_zero_get`: from a vanishing self-dot `Matrix.dot v v = 0`
each component `v[i]` is zero, specialising the fold lemma to the full index
list and the running form of `Matrix.dot`. -/
private theorem int_dot_self_eq_zero_get (v : Vector Int m)
    (hzero : Matrix.dot v v = 0) (i : Fin m) :
    v[i] = 0 := by
  have hmem : i ∈ List.finRange m := by simp
  exact foldl_int_dot_self_eq_zero_of_mem (xs := List.finRange m) (v := v)
    (acc := 0) (by decide)
    (by simpa [Matrix.dot, Hex.Vector.dotProduct] using hzero) i hmem

/-- If `v : Vector Int m` has zero self-dot product, then any other integer
vector dots it to zero from the left as well. -/
private theorem int_dot_eq_zero_of_dot_self_zero_left (u v : Vector Int m)
    (hzero : Matrix.dot v v = 0) :
    Matrix.dot v u = 0 := by
  unfold Matrix.dot Hex.Vector.dotProduct
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [int_dot_self_eq_zero_get v hzero i]
      have hzero_mul : (0 : Int) * u[i] = 0 := by grind
      rw [hzero_mul]
      have hadd_zero : (0 : Int) + 0 = 0 := by grind
      rw [hadd_zero]
      exact ih

/-- `foldl_dot_comm_int_local`: folding `u[i] * v[i]` over `xs` equals folding
`v[i] * u[i]` from an equal starting accumulator, the fold-level symmetry
underlying commutativity of the integer dot product. -/
private theorem foldl_dot_comm_int_local {n' : Nat} (xs : List (Fin n'))
    (u v : Vector Int n') (accU accV : Int) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind

/-- The dot product of integer vectors is commutative. (Local form for use
inside this file before the existing `dot_comm_int` declaration.) -/
private theorem int_dot_comm_local {n' : Nat} (u v : Vector Int n') :
    Matrix.dot u v = Matrix.dot v u := by
  simpa [Matrix.dot, Hex.Vector.dotProduct] using
    foldl_dot_comm_int_local (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

/-- Pointwise function equality for foldl-style sums lifts to a foldl equality. -/
private theorem foldl_add_pointwise_eq_int {α : Type v}
    (xs : List α) (f g : α → Int) (acc : Int)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y :=
        fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      exact ih (acc + g x) hxs

/-- Entry-level formula for `rowCombination` over integers: the `j`th entry is
the sum over `k` of `b[k][j] * c[k]`. -/
private theorem rowCombination_getElem_int
    {n m : Nat} (b : Matrix Int n m) (c : Vector Int n) (j : Fin m) :
    (Matrix.rowCombination b c)[j] =
      (List.finRange n).foldl (fun acc k => acc + b[k][j] * c[k]) 0 := by
  show (Matrix.transpose b * c)[j] = _
  rw [Matrix.mulVec_getElem]
  unfold Matrix.dot Hex.Vector.dotProduct
  apply foldl_add_pointwise_eq_int
  intro k _hk
  simp [Matrix.transpose, Matrix.col, Matrix.row]

/-- Distribute a constant `x : Int` through a foldl-style sum body. -/
private theorem foldl_mul_distrib_int {α : Type v}
    (xs : List α) (f : α → Int) (x acc : Int) :
    x * xs.foldl (fun acc y => acc + f y) acc =
      xs.foldl (fun acc y => acc + x * f y) (x * acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons y rest ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + f y)]
      have : x * (acc + f y) = x * acc + x * f y := by grind
      rw [this]

/-- Expansion of the dot product against `rowCombination` over integers: the
second argument's row combination distributes outside the sum, giving the
Σ-over-rows form. Proved via the `Hex.Matrix.foldl_det_sum_swap` Fubini
identity. -/
private theorem dot_rowCombination_right_eq
    {n m : Nat} (b : Matrix Int n m) (u : Vector Int m) (c : Vector Int n) :
    Matrix.dot u (Matrix.rowCombination b c) =
      (List.finRange n).foldl
        (fun acc k => acc + c[k] * Matrix.dot u (b.row k)) 0 := by
  -- Step 1: rewrite each (rowComb b c)[j] entry using rowCombination_getElem_int.
  have h_lhs :
      Matrix.dot u (Matrix.rowCombination b c) =
        (List.finRange m).foldl
          (fun accj j => accj + u[j] *
            (List.finRange n).foldl (fun acck k => acck + b[k][j] * c[k]) 0) 0 := by
    unfold Matrix.dot Hex.Vector.dotProduct
    apply foldl_add_pointwise_eq_int
    intro j _hj
    rw [rowCombination_getElem_int (b := b) (c := c) j]
  rw [h_lhs]
  -- Step 2: distribute u[j] over the inner sum so the body has shape (acc + f j k).
  have h_distrib :
      (List.finRange m).foldl
          (fun accj j => accj + u[j] *
            (List.finRange n).foldl (fun acck k => acck + b[k][j] * c[k]) 0) 0 =
        (List.finRange m).foldl
          (fun accj j => accj +
            (List.finRange n).foldl
              (fun acck k => acck + u[j] * (b[k][j] * c[k])) 0) 0 := by
    apply foldl_add_pointwise_eq_int
    intro j _hj
    have h_mul := foldl_mul_distrib_int (List.finRange n)
      (fun k : Fin n => b[k][j] * c[k]) u[j] 0
    have h_zero : u[j] * (0 : Int) = 0 := by grind
    rw [h_zero] at h_mul
    exact h_mul
  rw [h_distrib]
  -- Step 3: apply Fubini sum-swap.
  have h_swap :=
    Matrix.foldl_det_sum_swap (R := Int)
      (xs := List.finRange m) (ys := List.finRange n)
      (fun (j : Fin m) (k : Fin n) => u[j] * (b[k][j] * c[k]))
  rw [h_swap]
  -- Step 4: reshape each inner sum to match c[k] * dot u (b.row k).
  apply foldl_add_pointwise_eq_int
  intro k _hk
  -- We want:
  --   (List.finRange m).foldl (fun accj j => accj + u[j] * (b[k][j] * c[k])) 0
  --     = c[k] * Matrix.dot u (b.row k)
  -- Rearrange body so c[k] is the multiplier: u[j] * (b[k][j] * c[k])
  --     = c[k] * (u[j] * b[k][j]).
  have h_body :
      (List.finRange m).foldl
          (fun accj j => accj + u[j] * (b[k][j] * c[k])) 0 =
        (List.finRange m).foldl
          (fun accj j => accj + c[k] * (u[j] * b[k][j])) 0 := by
    apply foldl_add_pointwise_eq_int
    intro j _hj
    have : u[j] * (b[k][j] * c[k]) = c[k] * (u[j] * b[k][j]) := by grind
    exact this
  rw [h_body]
  -- Pull c[k] out of the foldl using foldl_mul_distrib_int (in reverse).
  have h_pull := foldl_mul_distrib_int (List.finRange m)
    (fun j : Fin m => u[j] * b[k][j]) c[k] 0
  have h_zero : c[k] * (0 : Int) = 0 := by grind
  rw [h_zero] at h_pull
  rw [← h_pull]
  -- Goal: c[k] * (List.finRange m).foldl (fun accj j => accj + u[j] * b[k][j]) 0
  --      = c[k] * Matrix.dot u (b.row k)
  -- Rewrite Matrix.dot definitionally to the foldl form using row entry equality.
  have h_dot_eq :
      Matrix.dot u (b.row k) =
        (List.finRange m).foldl (fun accj j => accj + u[j] * b[k][j]) 0 := by
    unfold Matrix.dot Hex.Vector.dotProduct
    apply foldl_add_pointwise_eq_int
    intro j _hj
    simp [Matrix.row]
  rw [h_dot_eq]

/-- A foldl-style sum whose every term is zero starting from a zero accumulator
collapses to zero. -/
private theorem foldl_add_zero {α : Type v}
    (xs : List α) (f : α → Int)
    (h : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) (0 : Int) = 0 := by
  have h_aux : ∀ (xs : List α) (acc : Int),
      (∀ x ∈ xs, f x = 0) →
        xs.foldl (fun acc x => acc + f x) acc = acc := by
    intro xs
    induction xs with
    | nil => intros acc _h; rfl
    | cons y rest ih =>
        intros acc h_terms
        simp only [List.foldl_cons]
        have hy : f y = 0 := h_terms y (by simp)
        have hxs : ∀ x ∈ rest, f x = 0 :=
          fun x hx => h_terms x (List.mem_cons_of_mem _ hx)
        rw [hy]
        have h_add : acc + (0 : Int) = acc := by grind
        rw [h_add]
        exact ih (acc) hxs
  exact h_aux xs 0 h

/-- Gram zero-pivot column suffix: if the no-pivot Bareiss pass over the Gram
matrix runs `s` steps without recording a singular step but the pivot entry
`matrix[s][s]` is zero, then every later row's entry in column `s` is zero
too. This is the `h_column_zero` premise consumed by
`noPivotLoop_initial_gram_findPivot?_eq_none_of_column_zero` to discharge the
executable `findPivot? = none` form needed by the row-pivoted Bareiss loop on
the Gram trajectory.

The argument: by the closed row-vector consumer, the represented pivot row has
integer support on indices `≤ s` and inner product zero against `b.row k` for
every `k.val ≤ s` (those matrix entries are either the zero pivot itself or
zeros left by earlier regular elimination steps). Linearity of dot against
`rowCombination` over the supported indices then gives `Matrix.dot v v = 0`,
and integer positive definiteness forces every dot against `v` to be zero.
Trailing-block symmetry transports
`state.matrix[sFin][i] = Matrix.dot v (b.row i) = 0` across the diagonal to
`state.matrix[i][sFin] = 0`. -/
private theorem leadingPrefix_gram_zero_pivot_column_zero
    {n m : Nat} (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (hquot : StepWitness b)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (h_zero :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0) :
    ∀ i : Fin n, s + 1 ≤ i.val →
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0 := by
  intro i hi
  let sFin : Fin n := ⟨s, Nat.lt_of_succ_lt hs⟩
  -- Final state of the loop and its `step = s` alignment.
  have h_step :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step = s :=
    noPivotLoop_initial_gram_step_eq b s hs h_prefix_none
  have h_state_step_le_sFin :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ sFin.val := by
    rw [h_step]; show s ≤ s; exact Nat.le_refl _
  -- The row-vector consumer aligns `matrix[sFin][j]` with
  -- `Matrix.dot v (b.row j)` for all columns `j`.
  obtain ⟨v, ⟨c, h_coeff_supp_above, hv_def⟩, h_dot_eq_matrix⟩ :=
    noPivotLoop_initial_gram_exists_rowVec b s hquot sFin h_state_step_le_sFin
  -- The represented row is orthogonal to `b.row k` for every `k.val ≤ s`:
  -- on `k.val = s`, the hypothesis `h_zero` gives a zero pivot dot, and on
  -- `k.val < s` the column was cleared by an earlier regular Bareiss step.
  have h_dot_zero_le : ∀ k : Fin n, k.val ≤ s →
      Matrix.dot v (b.row k) = 0 := by
    intro k hks
    rw [← h_dot_eq_matrix k]
    by_cases hk_eq : k.val = s
    · have h_k_eq_sFin : k = sFin := Fin.ext hk_eq
      rw [h_k_eq_sFin]
      exact h_zero
    · -- k.val < s, use column-zero helper at fuel = s, k as kFin, sFin as i.
      have hk_lt : k.val < s := Nat.lt_of_le_of_ne hks hk_eq
      have h_init_step_le :
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ k.val := by
        show 0 ≤ k.val
        exact Nat.zero_le _
      have h_k_lt_result :
          k.val < (Matrix.noPivotLoop s
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step := by
        rw [h_step]
        exact hk_lt
      have h_k_lt_sFin : k.val < sFin.val := hk_lt
      exact noPivotLoop_matrix_processed_col_eq_zero s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_prefix_none
        k.val h_init_step_le h_k_lt_result k rfl sFin h_k_lt_sFin
  -- `Matrix.dot v v = 0`: every term in the rowCombination expansion is zero.
  have h_dot_self_zero : Matrix.dot v v = 0 := by
    have h_expand_aux :
        Matrix.dot v (Matrix.rowCombination b c) =
          (List.finRange n).foldl
            (fun acc k => acc + c[k] * Matrix.dot v (b.row k))
            0 :=
      dot_rowCombination_right_eq b v c
    rw [← hv_def] at h_expand_aux
    rw [h_expand_aux]
    apply foldl_add_zero
    intro k _hk
    by_cases hks : k.val ≤ s
    · -- second factor is zero
      rw [h_dot_zero_le k hks]
      grind
    · -- first factor is zero
      have hk_gt : sFin.val < k.val := by show s < k.val; omega
      rw [h_coeff_supp_above k hk_gt]
      grind
  -- Transport across symmetry: `matrix[i][sFin] = matrix[sFin][i]`.
  have h_init_sym :
      ∀ a c : Fin n,
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ a.val →
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ c.val →
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[a][c] =
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[c][a] := by
    intros a c _ha _hc
    show (Matrix.gramMatrix b)[a][c] = (Matrix.gramMatrix b)[c][a]
    rw [Matrix.gramMatrix_getElem, Matrix.gramMatrix_getElem]
    exact int_dot_comm_local (Matrix.row b a) (Matrix.row b c)
  have h_symm :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][sFin] =
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[sFin][i] := by
    apply noPivotLoop_matrix_symm_preserve s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_init_sym i sFin
    · rw [h_step]; omega
    · rw [h_step]; show s ≤ s; exact Nat.le_refl _
  -- Now matrix[sFin][i] = dot v (b.row i) = 0 via integer positive definiteness.
  rw [h_symm, h_dot_eq_matrix i]
  exact int_dot_eq_zero_of_dot_self_zero_left (b.row i) v h_dot_self_zero

/-- Substitution helper for the diagonal `(i, i)` matrix entry under a Fin
equality. -/
private theorem matrix_diag_at_fin_eq {n : Nat} (M : Matrix Int n n)
    {i j : Fin n} (h : i = j) :
    M[i][i] = M[j][j] := by
  subst h; rfl

/-- If the `a`-fueled no-pivot Bareiss prefix already recorded a singular step,
that step persists into any longer pass. -/
private theorem noPivotLoop_extends_singularStep
    {n : Nat} (state : Matrix.BareissState n) (a b : Nat) (k : Fin n)
    (h_sing_a : (Matrix.noPivotLoop a state).singularStep = some k.val)
    (h_step_a : (Matrix.noPivotLoop a state).step = k.val)
    (h_zero_a : (Matrix.noPivotLoop a state).matrix[k][k] = 0)
    (hk : k.val + 1 < n) :
    Matrix.noPivotLoop (a + b) state = Matrix.noPivotLoop a state := by
  rw [Matrix.noPivotLoop_add a b state]
  have hDone : (Matrix.noPivotLoop a state).step + 1 < n := by
    rw [h_step_a]; exact hk
  have hp_zero :
      (Matrix.noPivotLoop a state).matrix[
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
    have h_fin :
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step_a
    exact (matrix_diag_at_fin_eq (Matrix.noPivotLoop a state).matrix h_fin).trans h_zero_a
  have h_sing_step : (Matrix.noPivotLoop a state).singularStep =
      some (Matrix.noPivotLoop a state).step := by
    rw [h_sing_a, h_step_a]
  exact Matrix.noPivotLoop_id_at_singular_fixedpoint (n := n) b
    (Matrix.noPivotLoop a state) hDone hp_zero h_sing_step

/-- From a partial no-pivot Bareiss pass on `M` recording a singular step at
index `s`, derive that the `s`-fueled prefix is non-singular, has reached
`step = s`, and has zero diagonal at `(s, s)`. -/
private theorem noPivotLoop_prefix_state_at_singular
    {n : Nat} (M : Matrix Int n n) (fuel s : Nat) (hs : s + 1 ≤ n)
    (h_sing : (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState M)).singularStep = some s) :
    (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).singularStep = none ∧
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s ∧
      (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState M)).matrix[
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)][
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)] = 0 := by
  have h_init_sing : (Matrix.noPivotInitialState M).singularStep = none := rfl
  have h_init_step : (Matrix.noPivotInitialState M).step = 0 := rfl
  have hsfuel : s < fuel := by
    have := noPivotLoop_singularStep_lt (n := n) fuel
      (Matrix.noPivotInitialState M) h_init_sing s h_sing
    rw [h_init_step] at this
    omega
  rcases noPivotLoop_singular_inv (n := n) s
      (Matrix.noPivotInitialState M) h_init_sing
    with h_none | ⟨k', h_sing_s, h_step_s, h_zero_s, h_klt⟩
  · have hS_step : (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s := by
      have h_room :
          (Matrix.noPivotInitialState M).step + s + 1 ≤ n := by
        rw [h_init_step]; omega
      have h_step := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        (n := n) s (Matrix.noPivotInitialState M) h_init_sing h_room h_none
      rw [h_step, h_init_step]; omega
    refine ⟨h_none, hS_step, ?_⟩
    rcases noPivotLoop_singular_inv (n := n) fuel
        (Matrix.noPivotInitialState M) h_init_sing
      with h_full_none | ⟨k, h_sing_full, h_step_full, h_zero_full, h_klt_full⟩
    · rw [h_full_none] at h_sing; nomatch h_sing
    · have hk_eq : k.val = s := by
        rw [h_sing_full] at h_sing
        exact Option.some.inj h_sing
      have hsn : s < n := Nat.lt_of_succ_le hs
      have h_full_eq :
          Matrix.noPivotLoop (s + (fuel - s)) (Matrix.noPivotInitialState M) =
            Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) := by
        congr 1; omega
      have h_split :
          Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) =
            Matrix.noPivotLoop (fuel - s)
              (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)) := by
        rw [← h_full_eq,
          Matrix.noPivotLoop_add s (fuel - s) (Matrix.noPivotInitialState M)]
      have h_diag_preserved :
          (Matrix.noPivotLoop (fuel - s)
              (Matrix.noPivotLoop s (Matrix.noPivotInitialState M))).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
        Matrix.noPivotLoop_diag_of_le_step (fuel - s)
          (Matrix.noPivotLoop s (Matrix.noPivotInitialState M))
          (⟨s, hsn⟩ : Fin n)
          (by rw [hS_step]; exact Nat.le_refl _)
      have h_full_diag_eq :
          (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] := by
        rw [h_split]; exact h_diag_preserved
      have h_fin : k = (⟨s, hsn⟩ : Fin n) := Fin.ext hk_eq
      have h_full_zero :
          (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix[
            (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] = 0 :=
        (matrix_diag_at_fin_eq
            (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix h_fin).symm.trans
          h_zero_full
      exact h_full_diag_eq.symm.trans h_full_zero
  · have h_klt' : k'.val < s := by
      have := noPivotLoop_singularStep_lt (n := n) s
        (Matrix.noPivotInitialState M) h_init_sing k'.val h_sing_s
      rw [h_init_step] at this
      omega
    have h_persist :
        Matrix.noPivotLoop (s + (fuel - s)) (Matrix.noPivotInitialState M) =
          Matrix.noPivotLoop s (Matrix.noPivotInitialState M) :=
      noPivotLoop_extends_singularStep (Matrix.noPivotInitialState M) s (fuel - s) k'
        h_sing_s h_step_s h_zero_s h_klt
    have h_fuel_eq : s + (fuel - s) = fuel := by omega
    rw [h_fuel_eq] at h_persist
    rw [h_persist] at h_sing
    rw [h_sing_s] at h_sing
    have hk'_eq : k'.val = s := Option.some.inj h_sing
    omega

/-- If the row-pivoted Bareiss loop is in a state where, after `a` regular
no-pivot iterations, the next pivot is zero and the column has no replacement,
the loop records the resulting step as singular regardless of any remaining
fuel beyond the triggering iteration. The partial-pass result is passed
explicitly as `result` to keep Fin-index proof terms uniform across the
induction. -/
private theorem pivotLoop_singularStep_some
    {n : Nat} :
    ∀ (a : Nat) (fuel : Nat) (state : Matrix.BareissState n)
      (result : Matrix.BareissState n)
      (_h_partial : Matrix.noPivotLoop a state = result),
      state.singularStep = none →
      a + 1 ≤ fuel →
      result.singularStep = none →
      (h_step_lt : result.step + 1 < n) →
      result.matrix[(⟨result.step, Nat.lt_of_succ_lt h_step_lt⟩ : Fin n)][
        (⟨result.step, Nat.lt_of_succ_lt h_step_lt⟩ : Fin n)] = 0 →
      Matrix.findPivot? result.matrix
        (⟨result.step, Nat.lt_of_succ_lt h_step_lt⟩ : Fin n) (result.step + 1) = none →
      (Matrix.pivotLoop fuel state).singularStep = some result.step := by
  intro a
  induction a with
  | zero =>
      intro fuel state result h_partial _h_init_sing hfuel _h_part_none hStepLt hp_zero
          h_find_none
      -- noPivotLoop 0 state = state.
      have h_state_eq : state = result := by
        rw [show state = Matrix.noPivotLoop 0 state from rfl, h_partial]
      subst h_state_eq
      rcases fuel with _ | fuel'
      · omega
      exact (Matrix.pivotLoop_singular_branch_no_pivot fuel' state hStepLt hp_zero h_find_none
        ▸ rfl)
  | succ a' ih =>
      intro fuel state result h_partial h_init_sing hfuel h_part_none hStepLt hp_zero
          h_find_none
      have hDone_state : state.step + 1 < n := by
        have hmono := noPivotLoop_step_monotone (a' + 1) state
        rw [h_partial] at hmono
        omega
      by_cases hp0_state : state.matrix[state.step][state.step] = 0
      · -- Singular first iteration contradicts result.singularStep = none.
        exfalso
        have h_sing_branch :
            Matrix.noPivotLoop (a' + 1) state =
              { state with singularStep := some state.step } :=
          Matrix.noPivotLoop_singular_branch a' state hDone_state hp0_state
        rw [h_sing_branch] at h_partial
        rw [← h_partial] at h_part_none
        simp at h_part_none
      · -- Regular first iteration: recurse on the updated state.
        have h_unfold_noPiv : Matrix.noPivotLoop (a' + 1) state =
            Matrix.noPivotLoop a'
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none } :=
          Matrix.noPivotLoop_regular_branch a' state hDone_state hp0_state
        rcases fuel with _ | fuel'
        · omega
        have h_fuel' : a' + 1 ≤ fuel' := by omega
        have h_unfold_piv : Matrix.pivotLoop (fuel' + 1) state =
            Matrix.pivotLoop fuel'
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none } :=
          Matrix.pivotLoop_regular_branch_no_swap fuel' state hDone_state hp0_state
        rw [h_unfold_piv]
        have h_next_partial :
            Matrix.noPivotLoop a'
              ({ step := state.step + 1
                 matrix := Matrix.stepMatrix state.matrix state.step
                   state.matrix[state.step][state.step] state.prevPivot
                 prevPivot := state.matrix[state.step][state.step]
                 rowSwaps := state.rowSwaps
                 singularStep := none } : Matrix.BareissState n) = result := by
          rw [← h_unfold_noPiv]; exact h_partial
        exact ih fuel'
          { step := state.step + 1
            matrix := Matrix.stepMatrix state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          result h_next_partial rfl h_fuel' h_part_none hStepLt hp_zero h_find_none

/-- Singular branch of the Gram leading-prefix Bareiss identification: if the
no-pivot Bareiss pass over the full Gram matrix records a singular step at index
`s` strictly before slot `r + 1`, the public row-pivoted Bareiss determinant of
the `(r + 1)` leading Gram prefix is `Nat.zero`. The proof translates the
column-zero suffix from the closed row invariant on the full trajectory to the
leading prefix via the no-pivot sync lemma, then derives `findPivot? = none` on
the prefix, so the row-pivoted Bareiss loop records the same singular step. -/
private theorem leadingPrefix_gram_bareiss_toNat_eq_zero
    {n m : Nat} (b : Matrix Int n m) (r : Nat) (hr : r < n)
    (hquot : StepWitness b)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop r
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    (Matrix.bareiss
      (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
        (Nat.succ_le_of_lt hr))).toNat = 0 := by
  let GM := Matrix.gramMatrix b
  let initGM := Matrix.noPivotInitialState GM
  let hK : r + 1 ≤ n := Nat.succ_le_of_lt hr
  let LP := Matrix.leadingPrefix GM (r + 1) hK
  let initLP := Matrix.noPivotInitialState LP
  -- Step 1: s < r via noPivotLoop_singularStep_lt.
  have hsr : s < r := by
    have h := noPivotLoop_singularStep_lt (n := n) r initGM rfl s h_sing
    change s < initGM.step + r at h
    have : initGM.step = 0 := rfl
    omega
  have hs1n : s + 1 < n := Nat.lt_of_lt_of_le (Nat.succ_lt_succ hsr) hr
  have hsn : s < n := Nat.lt_of_succ_lt hs1n
  -- Step 2: extract partial state at s iterations.
  have hsucc_n : s + 1 ≤ n := Nat.le_of_lt hs1n
  obtain ⟨h_full_none, h_full_step, h_full_zero⟩ :=
    noPivotLoop_prefix_state_at_singular GM r s hsucc_n h_sing
  -- Step 3: column-zero on FULL via leadingPrefix_gram_zero_pivot_column_zero.
  have h_full_col_zero :
      ∀ i : Fin n, s + 1 ≤ i.val →
        (Matrix.noPivotLoop s initGM).matrix[i][(⟨s, hsn⟩ : Fin n)] = 0 :=
    leadingPrefix_gram_zero_pivot_column_zero
      (b := b) s hs1n hquot h_full_none h_full_zero
  -- Step 4: sync — leadingPrefix (noPivotLoop s initGM).matrix (r+1) = (noPivotLoop s initLP).matrix.
  have h_sync :=
    noPivotLoop_sync_leadingPrefix_aux (n := n) (K := r + 1) hK s
      initGM initLP rfl rfl rfl rfl
      (by
        show Matrix.leadingPrefix initGM.matrix (r + 1) hK = initLP.matrix
        rfl)
      (show s + initGM.step < r + 1 by
        change s + 0 < r + 1; omega)
  obtain ⟨h_step_sync, _h_prev_sync, _h_rows_sync, h_sing_sync, h_mat_sync⟩ := h_sync
  -- Useful Fin bound.
  have hs_lt_r1 : s < r + 1 := Nat.lt_succ_of_lt hsr
  -- Step 5: translate column-zero to LP.
  have h_LP_col_zero :
      ∀ i' : Fin (r + 1), s + 1 ≤ i'.val →
        (Matrix.noPivotLoop s initLP).matrix[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] = 0 := by
    intro i' hi'
    let iN : Fin n := ⟨i'.val, Nat.lt_of_lt_of_le i'.isLt hK⟩
    have h_LP_entry :
        (Matrix.noPivotLoop s initLP).matrix[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] =
        (Matrix.leadingPrefix (Matrix.noPivotLoop s initGM).matrix (r + 1) hK)[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] := by
      rw [← h_mat_sync]
    rw [h_LP_entry]
    rw [Matrix.leadingPrefix_entry (Matrix.noPivotLoop s initGM).matrix (r + 1) hK i'
      (⟨s, hs_lt_r1⟩ : Fin (r + 1))]
    have hi_iN : s + 1 ≤ iN.val := hi'
    have h_col_zero_iN := h_full_col_zero iN hi_iN
    have h_entry_eq :
        (Matrix.noPivotLoop s initGM).matrix[iN][
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)] =
        (Matrix.noPivotLoop s initGM).matrix[iN][(⟨s, hsn⟩ : Fin n)] :=
      congrArg (fun (j : Fin n) => (Matrix.noPivotLoop s initGM).matrix[iN][j])
        (Fin.ext (rfl : (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n).val =
                        (⟨s, hsn⟩ : Fin n).val))
    exact h_entry_eq.trans h_col_zero_iN
  -- Step 6: findPivot? = none on LP.
  have h_LP_step : (Matrix.noPivotLoop s initLP).step = s := by
    rw [← h_step_sync]; exact h_full_step
  have h_LP_sing : (Matrix.noPivotLoop s initLP).singularStep = none := by
    rw [← h_sing_sync]; exact h_full_none
  have h_LP_zero_diag :
      (Matrix.noPivotLoop s initLP).matrix[(⟨s, hs_lt_r1⟩ : Fin (r + 1))][
        (⟨s, hs_lt_r1⟩ : Fin (r + 1))] = 0 := by
    have h_LP_entry :
        (Matrix.noPivotLoop s initLP).matrix[(⟨s, hs_lt_r1⟩ : Fin (r + 1))][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] =
        (Matrix.leadingPrefix (Matrix.noPivotLoop s initGM).matrix (r + 1) hK)[
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] := by
      rw [← h_mat_sync]
    rw [h_LP_entry]
    rw [Matrix.leadingPrefix_entry (Matrix.noPivotLoop s initGM).matrix (r + 1) hK
      (⟨s, hs_lt_r1⟩ : Fin (r + 1)) (⟨s, hs_lt_r1⟩ : Fin (r + 1))]
    have h_idx_eq :
        (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n) =
          (⟨s, hsn⟩ : Fin n) := Fin.ext rfl
    have h_entry_eq :
        (Matrix.noPivotLoop s initGM).matrix[
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)][
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)] =
        (Matrix.noPivotLoop s initGM).matrix[(⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
      matrix_diag_at_fin_eq _ h_idx_eq
    exact h_entry_eq.trans h_full_zero
  have h_LP_find_none :
      Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
        (⟨s, hs_lt_r1⟩ : Fin (r + 1)) (s + 1) = none :=
    Matrix.findPivot?_eq_none_of_zero _ _ _ h_LP_col_zero
  -- Step 7: pivotLoop on LP records singular at s.
  have h_LP_step_lt : (Matrix.noPivotLoop s initLP).step + 1 < r + 1 := by
    rw [h_LP_step]; omega
  have h_idx_at_LP_step :
      (⟨(Matrix.noPivotLoop s initLP).step,
        Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1)) =
        (⟨s, hs_lt_r1⟩ : Fin (r + 1)) :=
    Fin.ext h_LP_step
  have h_LP_zero_at_result :
      (Matrix.noPivotLoop s initLP).matrix[
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))][
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))] = 0 :=
    (matrix_diag_at_fin_eq (n := r + 1)
      (Matrix.noPivotLoop s initLP).matrix h_idx_at_LP_step).trans h_LP_zero_diag
  have h_LP_find_at_result :
      Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))
        ((Matrix.noPivotLoop s initLP).step + 1) = none := by
    have h_step_plus_eq : (Matrix.noPivotLoop s initLP).step + 1 = s + 1 := by
      rw [h_LP_step]
    have h_step1 :
        Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨(Matrix.noPivotLoop s initLP).step,
              Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) =
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) :=
      congrArg
        (fun (i : Fin (r + 1)) =>
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix i
            ((Matrix.noPivotLoop s initLP).step + 1))
        h_idx_at_LP_step
    have h_step2 :
        Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) =
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            (s + 1) :=
      congrArg
        (fun (st : Nat) =>
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1)) st)
        h_step_plus_eq
    exact (h_step1.trans h_step2).trans h_LP_find_none
  have h_pivot_sing : (Matrix.pivotLoop (r + 1) initLP).singularStep =
      some (Matrix.noPivotLoop s initLP).step :=
    pivotLoop_singularStep_some
      s (r + 1) initLP (Matrix.noPivotLoop s initLP)
      rfl rfl (by omega) h_LP_sing h_LP_step_lt
      h_LP_zero_at_result h_LP_find_at_result
  -- Step 8: bareiss LP = 0 via singular branch of BareissData.det.
  have h_bareissData_sing :
      (Matrix.bareissData LP).singularStep =
        some (Matrix.noPivotLoop s initLP).step := by
    rw [Matrix.bareissData_eq_finish_pivotLoop]
    show (Matrix.pivotLoop (r + 1) initLP).singularStep =
      some (Matrix.noPivotLoop s initLP).step
    exact h_pivot_sing
  have h_bareiss_zero : Matrix.bareiss LP = 0 := by
    rw [Matrix.bareiss_eq_bareissData_det]
    unfold Matrix.BareissData.det
    rw [h_bareissData_sing]
  show (Matrix.bareiss LP).toNat = 0
  rw [h_bareiss_zero]
  rfl

/-- If the array loop's `state.step` is past the matrix extent, one outer
iteration returns the input state unchanged. -/
private theorem scaledCoeffArrayLoop_done (fuel : Nat)
    (state : ScaledCoeffArrayState) (hDone : ¬ state.step < n) :
    scaledCoeffArrayLoop n (fuel + 1) state = state := by
  simp [scaledCoeffArrayLoop, hDone]

/-- The array loop is idempotent once `state.step ≥ n`. -/
private theorem scaledCoeffArrayLoop_id_at_done (fuel : Nat)
    (state : ScaledCoeffArrayState) (hDone : ¬ state.step < n) :
    scaledCoeffArrayLoop n fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ f => exact scaledCoeffArrayLoop_done f state hDone

/-- Singular branch of one array-loop iteration: a zero pivot strictly before
the last column halts the loop, writing the scaled column at the current step
but leaving the matrix and step untouched. -/
private theorem scaledCoeffArrayLoop_singular_branch (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step = 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      { state with coeffs := writeScaledColumn state.coeffs state.matrix n state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]

/-- Last-column branch of one array-loop iteration: when `state.step = n - 1`,
the loop writes the final scaled column and advances `step` to `n` without
applying a Bareiss step. -/
private theorem scaledCoeffArrayLoop_last_step (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : ¬ state.step + 1 < n) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      { state with
        step := state.step + 1
        coeffs := writeScaledColumn state.coeffs state.matrix n state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext]

/-- Regular branch of one array-loop iteration: a nonzero pivot strictly before
the last column applies one row-mutating Bareiss update, advances
`step`, records the new `prevPivot`, and recurses on the remaining fuel. -/
private theorem scaledCoeffArrayLoop_regular_branch (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step ≠ 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      scaledCoeffArrayLoop n fuel
        { step := state.step + 1
          matrix := stepScaledRows state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]

/-- The matrix-side view of a row-storage entry: `getArrayEntry` on the array
matches the matrix-level `[i][j]` lookup under `rowsToMatrix`. -/
private theorem getArrayEntry_eq_rowsToMatrix
    (rows : Array (Array Int)) (i j : Fin n) :
    getArrayEntry rows i.val j.val = (rowsToMatrix rows n)[i][j] := by
  simp [rowsToMatrix, Matrix.ofFn]

/-- If the array loop is currently at column `j`, the coefficient entry below
the diagonal in that column records the pre-elimination matrix entry for that
same step. In the regular branch, later recursive iterations preserve column
`j` because the next state has advanced past it. -/
private theorem getArrayEntry_scaledCoeffArrayLoop_current_col_written
    (n fuel : Nat) (state : ScaledCoeffArrayState) (i j : Nat)
    (hstep : state.step = j) (hji : j < i) (hin : i < n)
    (h_coeffs_size : state.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state.coeffs[r]!.size = n) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state).coeffs i j =
      getArrayEntry state.matrix i j := by
  have hArrayStep : state.step < n := by omega
  have hrow : i < state.coeffs.size := by
    rw [h_coeffs_size]
    exact hin
  have hcol : j < state.coeffs[i]!.size := by
    rw [h_coeffs_rows_size i hin]
    exact Nat.lt_trans hji hin
  by_cases hNext : state.step + 1 < n
  · by_cases hp : getArrayEntry state.matrix state.step state.step = 0
    · rw [scaledCoeffArrayLoop_singular_branch fuel state hArrayStep hNext hp]
      rw [hstep]
      exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n j i
        hji hin hrow hcol
    · rw [scaledCoeffArrayLoop_regular_branch fuel state hArrayStep hNext hp]
      let next : ScaledCoeffArrayState :=
        { step := state.step + 1
          matrix := stepScaledRows state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step }
      change getArrayEntry (scaledCoeffArrayLoop n fuel next).coeffs i j =
        getArrayEntry state.matrix i j
      rw [getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step]
      · show getArrayEntry (writeScaledColumn state.coeffs state.matrix n state.step) i j =
          getArrayEntry state.matrix i j
        rw [hstep]
        exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n j i
          hji hin hrow hcol
      · show j < next.step
        simp [next, hstep]
  · rw [scaledCoeffArrayLoop_last_step fuel state hArrayStep hNext]
    rw [hstep]
    exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n j i
      hji hin hrow hcol

/-- Size preservation: the inner `coeffs` array of the scaled-coefficient
array loop keeps its outer-array length. -/
private theorem scaledCoeffArrayLoop_coeffs_size
    (fuel : Nat) (state : ScaledCoeffArrayState) :
    (scaledCoeffArrayLoop n fuel state).coeffs.size = state.coeffs.size := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      unfold scaledCoeffArrayLoop
      by_cases h_step : state.step < n
      · simp only [h_step, ↓reduceIte]
        by_cases h_next : state.step + 1 < n
        · simp only [h_next, ↓reduceIte]
          by_cases h_pivot : getArrayEntry state.matrix state.step state.step = 0
          · simp only [h_pivot, ↓reduceIte]
            exact writeScaledColumn_size _ _ _ _
          · simp only [h_pivot, ↓reduceIte]
            rw [ih]
            exact writeScaledColumn_size _ _ _ _
        · simp only [h_next, ↓reduceIte]
          exact writeScaledColumn_size _ _ _ _
      · simp only [h_step, ↓reduceIte]

/-- Bareiss-side counterpart of the Schur `j = 0` boundary: at column `0`,
the scaled-coefficient array records the gram entry `gram[i][0]` at every
row `i`. The first `writeScaledColumn` call captures the initial gram column;
subsequent loop iterations advance past column `0` and preserve it. -/
private theorem getArrayEntry_scaledCoeffRows_col_zero
    (b : Matrix Int n m) (i : Nat) :
    getArrayEntry (scaledCoeffRows b) i 0 =
      getArrayEntry (gramRows b) i 0 := by
  by_cases hin : i < n
  · -- In bounds. n ≥ 1 (since `i < n`), so the array loop unfolds at least
    -- one step. The first iteration writes column 0 from `gramRows b`, and
    -- later iterations have `step ≥ 1` so they preserve column 0.
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hin
    obtain ⟨fuel, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h_coeffs_size : (zeroRows (fuel + 1)).size = fuel + 1 := zeroRows_size _
    have h_coeffs_row_size :
        ∀ r, r < fuel + 1 → (zeroRows (fuel + 1))[r]!.size = fuel + 1 :=
      fun r hr => zeroRows_row_size _ r hr
    let initState : ScaledCoeffArrayState :=
      { step := 0, matrix := gramRows b, coeffs := zeroRows (fuel + 1),
        prevPivot := 1 }
    by_cases hi : i = 0
    · -- Diagonal case: (0, 0). Unfold one step and use writeScaledColumn_diag.
      subst hi
      have hrow : (0 : Nat) < (zeroRows (fuel + 1)).size := by
        rw [h_coeffs_size]; exact hn
      have hcol : (0 : Nat) < (zeroRows (fuel + 1))[0]!.size := by
        rw [zeroRows_row_size _ 0 hn]; exact hn
      show getArrayEntry (scaledCoeffArrayLoop (fuel + 1) (fuel + 1) initState).coeffs 0 0
          = getArrayEntry (gramRows b) 0 0
      by_cases hNext : (0 : Nat) + 1 < fuel + 1
      · by_cases hp : getArrayEntry (gramRows b) 0 0 = 0
        · rw [scaledCoeffArrayLoop_singular_branch (n := fuel + 1) fuel initState hn hNext hp]
          exact getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol
        · rw [scaledCoeffArrayLoop_regular_branch (n := fuel + 1) fuel initState hn hNext hp]
          rw [getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step
                (n := fuel + 1) fuel _ 0 0 (show (0 : Nat) < 0 + 1 by omega)]
          exact getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol
      · rw [scaledCoeffArrayLoop_last_step (n := fuel + 1) fuel initState hn hNext]
        exact getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol
    · -- Strict lower (0 < i < n). Reuse the existing current-col capture lemma.
      have hji : 0 < i := Nat.pos_of_ne_zero hi
      show getArrayEntry (scaledCoeffArrayLoop (fuel + 1) (fuel + 1) initState).coeffs i 0
          = getArrayEntry (gramRows b) i 0
      exact getArrayEntry_scaledCoeffArrayLoop_current_col_written
        (n := fuel + 1) fuel initState i 0 (by rfl) hji hin h_coeffs_size h_coeffs_row_size
  · -- Out of bounds. The array loop never grows `coeffs.size`, so `(i, 0)`
    -- stays at the initial zero (and so does `(gramRows b)[i][0]`).
    have hin' : n ≤ i := Nat.le_of_not_lt hin
    have h_final_size : (scaledCoeffRows b).size = n := by
      unfold scaledCoeffRows
      rw [scaledCoeffArrayLoop_coeffs_size]
      exact zeroRows_size n
    have h_gram_size : (gramRows b).size = n := gramRows_size b
    have h_lhs : getArrayEntry (scaledCoeffRows b) i 0 = 0 := by
      have h_size_le : (scaledCoeffRows b).size ≤ i := h_final_size.symm ▸ hin'
      have h_entry_default : (scaledCoeffRows b)[i]! = (default : Array Int) := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none h_size_le, Option.getD_none]
      unfold getArrayEntry
      rw [h_entry_default]
      exact getArrayEntry_default_row 0
    have h_rhs : getArrayEntry (gramRows b) i 0 = 0 := by
      have h_size_le : (gramRows b).size ≤ i := h_gram_size.symm ▸ hin'
      have h_entry_default : (gramRows b)[i]! = (default : Array Int) := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none h_size_le, Option.getD_none]
      unfold getArrayEntry
      rw [h_entry_default]
      exact getArrayEntry_default_row 0
    rw [h_lhs, h_rhs]

/-- Non-singular target-column lower-triangle capture. If the matrix-side
`noPivotLoop` reaches the target column `j` without recording a singular step,
then the scaled-coefficient array loop records at `(i,j)` the matrix entry from
the pre-elimination state at that target column. -/
private theorem scaledCoeffArrayLoop_lower_matches_target_column
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (h_array_size : state_array.matrix.size = n)
    (h_array_rows_size : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (fuel : Nat) (i j : Fin n)
    (h_step_le_j : state_matrix.step ≤ j.val)
    (hji : j.val < i.val)
    (h_fuel : j.val < state_matrix.step + fuel)
    (h_target_nonsing :
      (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).singularStep = none) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val j.val =
      (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).matrix[i][j] := by
  induction fuel generalizing state_array state_matrix with
  | zero =>
      omega
  | succ fuel' ih =>
      by_cases h_at_target : state_matrix.step = j.val
      · have h_array_step : state_array.step = j.val := by
          rw [h_step_eq, h_at_target]
        rw [getArrayEntry_scaledCoeffArrayLoop_current_col_written n fuel' state_array
          i.val j.val h_array_step hji i.isLt h_coeffs_size h_coeffs_rows_size]
        have hdist : j.val - state_matrix.step = 0 := by omega
        rw [hdist, Matrix.noPivotLoop_zero_fuel]
        rw [getArrayEntry_eq_rowsToMatrix state_array.matrix i j]
        rw [h_matrix_eq]
      · have h_step_lt_j : state_matrix.step < j.val :=
          Nat.lt_of_le_of_ne h_step_le_j h_at_target
        have hDone : state_matrix.step + 1 < n := by
          omega
        have h_step_lt_n : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hArrayStep : state_array.step < n := h_step_eq ▸ h_step_lt_n
        have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
        let kFin : Fin n := ⟨state_matrix.step, h_step_lt_n⟩
        have h_pivot_array_eq_matrix :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [h_step_eq]
          have := getArrayEntry_eq_rowsToMatrix (n := n) state_array.matrix kFin kFin
          rw [this, h_matrix_eq]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        · have hdist :
              j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
            omega
          rw [hdist, Matrix.noPivotLoop_singular_branch _ state_matrix hDone hp] at h_target_nonsing
          simp at h_target_nonsing
        · have hp_array :
              getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [h_pivot_array_eq_matrix]
            exact hp
          rw [scaledCoeffArrayLoop_regular_branch fuel' state_array hArrayStep hArrayNext hp_array]
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          change getArrayEntry (scaledCoeffArrayLoop n fuel' new_array).coeffs i.val j.val =
            (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).matrix[i][j]
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [h_step_eq]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _ state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [rowsToMatrix_stepScaledRows_eq _ _ _ _ h_array_size
              h_array_rows_size, h_matrix_eq, h_pivot_array_eq_matrix, h_step_eq, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot := h_pivot_array_eq_matrix
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [stepScaledRows_size, h_array_size]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _ _)[r]!.size = n
            exact stepScaledRows_rows_size state_array.matrix n state_array.step _ _
              h_array_size h_array_rows_size r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [writeScaledColumn_size]
            exact h_coeffs_size
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [writeScaledColumn_rows_size]
            exact h_coeffs_rows_size r hr
          have h_step_le_j_new : new_matrix.step ≤ j.val := by
            show state_matrix.step + 1 ≤ j.val
            omega
          have h_fuel_new : j.val < new_matrix.step + fuel' := by
            show j.val < state_matrix.step + 1 + fuel'
            omega
          have h_target_nonsing_new :
              (Matrix.noPivotLoop (j.val - new_matrix.step) new_matrix).singularStep = none := by
            have hdist :
                j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
              omega
            rw [hdist, Matrix.noPivotLoop_regular_branch _ state_matrix hDone hp] at h_target_nonsing
            simpa [new_matrix] using h_target_nonsing
          have h_capture := ih h_step_new h_matrix_new h_prev_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_step_le_j_new h_fuel_new h_target_nonsing_new
          have hdist :
              j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
            omega
          rw [h_capture]
          rw [hdist, Matrix.noPivotLoop_regular_branch _ state_matrix hDone hp]
          rfl

/-- Early-singular zero tail after the singular column: if the lower entries
in columns strictly after the current step are still unwritten before the
singular branch, writing the current column preserves that zero tail. -/
private theorem scaledCoeffArrayLoop_lower_singular_after_step
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_coeffs_unwritten : ∀ r c : Fin n,
      state_matrix.step < c.val → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = 0)
    (fuel : Nat) (i j : Fin n)
    (hsj : state_matrix.step < j.val) (hji : j.val < i.val)
    (hDone : state_matrix.step + 1 < n)
    (hp : state_matrix.matrix[
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs i.val j.val = 0 := by
  have hArrayStep : state_array.step < n := h_step_eq ▸ Nat.lt_of_succ_lt hDone
  have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
  let kFin : Fin n := ⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩
  have hp_array :
      getArrayEntry state_array.matrix state_array.step state_array.step = 0 := by
    rw [h_step_eq]
    have := getArrayEntry_eq_rowsToMatrix (n := n) state_array.matrix kFin kFin
    rw [this, h_matrix_eq]
    exact hp
  rw [scaledCoeffArrayLoop_singular_branch fuel state_array hArrayStep hArrayNext hp_array]
  rw [getArrayEntry_writeScaledColumn]
  · exact h_coeffs_unwritten i j hsj hji
  · rw [h_step_eq]
    omega

/-- Singular dual of `scaledCoeffArrayLoop_lower_matches_target_column`.
When the matrix-side `noPivotLoop` records a singular step strictly before
reaching column `j`, the array loop halts at the singular column and the
target column is left at its initial (unwritten) zero value. -/
private theorem scaledCoeffArrayLoop_lower_zero
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (h_array_size : state_array.matrix.size = n)
    (h_array_rows_size : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (h_coeffs_unwritten : ∀ r c : Fin n,
      state_matrix.step < c.val → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = 0)
    (h_no_sing : state_matrix.singularStep = none)
    (fuel : Nat) (i j : Fin n)
    (h_step_le_j : state_matrix.step ≤ j.val)
    (hji : j.val < i.val)
    (h_fuel : j.val < state_matrix.step + fuel)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).singularStep
        = some s) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val j.val = 0 := by
  induction fuel generalizing state_array state_matrix with
  | zero => omega
  | succ fuel' ih =>
      by_cases h_at_target : state_matrix.step = j.val
      · have hdist : j.val - state_matrix.step = 0 := by omega
        rw [hdist, Matrix.noPivotLoop_zero_fuel] at h_sing
        rw [h_no_sing] at h_sing
        nomatch h_sing
      · have h_step_lt_j : state_matrix.step < j.val :=
          Nat.lt_of_le_of_ne h_step_le_j h_at_target
        have hDone : state_matrix.step + 1 < n := by
          have := i.isLt
          omega
        have h_step_lt_n : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hArrayStep : state_array.step < n := h_step_eq ▸ h_step_lt_n
        have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
        let kFin : Fin n := ⟨state_matrix.step, h_step_lt_n⟩
        have h_pivot_array_eq_matrix :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [h_step_eq]
          have := getArrayEntry_eq_rowsToMatrix (n := n) state_array.matrix kFin kFin
          rw [this, h_matrix_eq]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        · exact scaledCoeffArrayLoop_lower_singular_after_step
            (n := n) (state_array := state_array) (state_matrix := state_matrix)
            h_step_eq h_matrix_eq h_coeffs_unwritten fuel' i j h_step_lt_j hji hDone hp
        · have hp_array :
              getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [h_pivot_array_eq_matrix]
            exact hp
          rw [scaledCoeffArrayLoop_regular_branch fuel' state_array hArrayStep
            hArrayNext hp_array]
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n
                state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          change getArrayEntry (scaledCoeffArrayLoop n fuel' new_array).coeffs i.val j.val = 0
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [h_step_eq]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _
                  state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [rowsToMatrix_stepScaledRows_eq _ _ _ _ h_array_size
              h_array_rows_size, h_matrix_eq, h_pivot_array_eq_matrix, h_step_eq, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot :=
            h_pivot_array_eq_matrix
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [stepScaledRows_size, h_array_size]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _
              state_array.prevPivot)[r]!.size = n
            exact stepScaledRows_rows_size state_array.matrix n state_array.step _ _
              h_array_size h_array_rows_size r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [writeScaledColumn_size]
            exact h_coeffs_size
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [writeScaledColumn_rows_size]
            exact h_coeffs_rows_size r hr
          have h_coeffs_unwritten_new : ∀ r c : Fin n,
              new_matrix.step < c.val → c.val < r.val →
                getArrayEntry new_array.coeffs r.val c.val = 0 := by
            intro r c hsc hcr
            show getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n
                  state_array.step) r.val c.val = 0
            have hsc' : state_matrix.step + 1 < c.val := hsc
            have hc_ne_step : c.val ≠ state_array.step := by
              rw [h_step_eq]; omega
            rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _ hc_ne_step]
            exact h_coeffs_unwritten r c (by omega) hcr
          have h_no_sing_new : new_matrix.singularStep = none := rfl
          have h_step_le_j_new : new_matrix.step ≤ j.val := by
            show state_matrix.step + 1 ≤ j.val
            omega
          have h_fuel_new : j.val < new_matrix.step + fuel' := by
            show j.val < state_matrix.step + 1 + fuel'
            omega
          have h_sing_new :
              (Matrix.noPivotLoop (j.val - new_matrix.step) new_matrix).singularStep
                = some s := by
            have hdist :
                j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
              omega
            rw [hdist, Matrix.noPivotLoop_regular_branch _ state_matrix hDone hp] at h_sing
            simpa [new_matrix] using h_sing
          exact ih h_step_new h_matrix_new h_prev_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_coeffs_unwritten_new h_no_sing_new h_step_le_j_new h_fuel_new
            h_sing_new

/-- State-level diagonal correspondence between the scaled-coefficient array
loop and the matrix-level `Matrix.noPivotLoop` on the same Gram-like data.

After running both loops for `fuel` iterations from compatible starting states
(matching steps, matrices, and `prevPivot`, with no recorded singular step
upstream and the coeffs invariant for already-processed columns), the
diagonal coefficient at every position `i` either matches the matrix-level
diagonal of `noPivotLoop` (when no singular step has been hit at or before
`i`) or is recorded as zero (when singular at some `s ≤ i`). This captures
the loop-level interpretation of `gramDetVecEntry` against the executable
array trajectory. -/
private theorem scaledCoeffArrayLoop_diag_matches
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (h_no_sing : state_matrix.singularStep = none)
    (h_array_size : state_array.matrix.size = n)
    (h_array_rows_size : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (h_coeffs_processed : ∀ j (_hjs : j < state_matrix.step) (hjn : j < n),
      getArrayEntry state_array.coeffs j j =
        state_matrix.matrix[(⟨j, hjn⟩ : Fin n)][(⟨j, hjn⟩ : Fin n)])
    (h_coeffs_unwritten : ∀ j (_hjs : state_matrix.step ≤ j) (_hjn : j < n),
      getArrayEntry state_array.coeffs j j = 0)
    (fuel : Nat) (i : Fin n)
    (h_fuel : i.val < state_matrix.step + fuel ∨ i.val < state_matrix.step) :
    ((Matrix.noPivotLoop fuel state_matrix).singularStep = none ∧
      getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val =
        (Matrix.noPivotLoop fuel state_matrix).matrix[i][i]) ∨
    (∃ s : Nat,
      (Matrix.noPivotLoop fuel state_matrix).singularStep = some s ∧
      ((s ≤ i.val ∧
        getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val = 0) ∨
       (i.val < s ∧
        getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val =
          (Matrix.noPivotLoop fuel state_matrix).matrix[i][i]))) := by
  induction fuel generalizing state_array state_matrix with
  | zero =>
      left
      refine ⟨h_no_sing, ?_⟩
      have h_ilt : i.val < state_matrix.step := by
        rcases h_fuel with hor1 | hor2
        · simpa using hor1
        · exact hor2
      exact h_coeffs_processed i.val h_ilt i.isLt
  | succ fuel' ih =>
      by_cases hDone : state_matrix.step + 1 < n
      · -- Subcase A: state_matrix.step + 1 < n. One real iteration.
        have h_step_lt_n : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hArrayStep : state_array.step < n := h_step_eq ▸ h_step_lt_n
        have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
        -- Build the pivot Fin index once.
        let kFin : Fin n := ⟨state_matrix.step, h_step_lt_n⟩
        -- Identify pivot equality between array and matrix views.
        have h_pivot_array_eq_matrix :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [h_step_eq]
          have := getArrayEntry_eq_rowsToMatrix (n := n) state_array.matrix kFin kFin
          rw [this, h_matrix_eq]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        · -- A1: singular branch.
          have hp_array : getArrayEntry state_array.matrix state_array.step state_array.step = 0 := by
            rw [h_pivot_array_eq_matrix]; exact hp
          rw [scaledCoeffArrayLoop_singular_branch fuel' state_array hArrayStep hArrayNext hp_array]
          rw [Matrix.noPivotLoop_singular_branch fuel' state_matrix hDone hp]
          right
          refine ⟨state_matrix.step, rfl, ?_⟩
          by_cases h_ilt : i.val < state_matrix.step
          · right
            refine ⟨h_ilt, ?_⟩
            change getArrayEntry
              (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
              state_matrix.matrix[i][i]
            rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _
              (show i.val ≠ state_array.step by rw [h_step_eq]; omega)]
            exact h_coeffs_processed i.val h_ilt i.isLt
          · have h_ilt : state_matrix.step ≤ i.val := Nat.le_of_not_lt h_ilt
            by_cases h_ieq : i.val = state_matrix.step
            · left
              refine ⟨Nat.le_of_eq h_ieq.symm, ?_⟩
              change getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                0
              have h_array_step_eq_i : state_array.step = i.val := by
                rw [h_step_eq]; exact h_ieq.symm
              rw [h_array_step_eq_i]
              have hrow : i.val < state_array.coeffs.size := by
                rw [h_coeffs_size]; exact i.isLt
              have hcol : i.val < state_array.coeffs[i.val]!.size := by
                rw [h_coeffs_rows_size i.val i.isLt]; exact i.isLt
              rw [getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol]
              -- Goal: getArrayEntry state_array.matrix i.val i.val = 0
              rw [← h_array_step_eq_i]
              exact hp_array
            · have h_igt : state_matrix.step < i.val :=
                Nat.lt_of_le_of_ne h_ilt fun h => h_ieq h.symm
              left
              refine ⟨Nat.le_of_lt h_igt, ?_⟩
              change getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                0
              rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _
                (show i.val ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_unwritten i.val (Nat.le_of_lt h_igt) i.isLt
        · -- A2: regular branch.
          have hp_array : getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [h_pivot_array_eq_matrix]; exact hp
          rw [scaledCoeffArrayLoop_regular_branch fuel' state_array hArrayStep hArrayNext hp_array]
          rw [Matrix.noPivotLoop_regular_branch fuel' state_matrix hDone hp]
          -- Build new compatible states.
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [h_step_eq]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _ state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [rowsToMatrix_stepScaledRows_eq _ _ _ _ h_array_size
              h_array_rows_size, h_matrix_eq, h_pivot_array_eq_matrix, h_step_eq, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot := h_pivot_array_eq_matrix
          have h_no_sing_new : new_matrix.singularStep = none := rfl
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [stepScaledRows_size, h_array_size]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _ _)[r]!.size = n
            exact stepScaledRows_rows_size state_array.matrix n state_array.step _ _
              h_array_size h_array_rows_size r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [writeScaledColumn_size]; exact h_coeffs_size
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [writeScaledColumn_rows_size]; exact h_coeffs_rows_size r hr
          have h_coeffs_processed_new :
              ∀ j (_hjs : j < new_matrix.step) (hjn : j < n),
                getArrayEntry new_array.coeffs j j =
                  new_matrix.matrix[(⟨j, hjn⟩ : Fin n)][(⟨j, hjn⟩ : Fin n)] := by
            intro j hjs hjn
            let jFin : Fin n := ⟨j, hjn⟩
            change getArrayEntry (writeScaledColumn _ _ _ _) j j =
              (Matrix.stepMatrix state_matrix.matrix _ _ state_matrix.prevPivot)[jFin][jFin]
            have hj_le : jFin.val ≤ state_matrix.step := Nat.le_of_lt_succ hjs
            rw [Matrix.stepMatrix_diag_of_le _ _ _ _ _ hj_le]
            by_cases hj_eq : j = state_matrix.step
            · -- j = state_matrix.step = state_array.step
              have h_array_step_eq_j : state_array.step = j := h_step_eq.trans hj_eq.symm
              -- Rewrite writeScaledColumn's step argument to use j.
              have h_write_eq :
                  getArrayEntry
                      (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) j j =
                    getArrayEntry
                      (writeScaledColumn state_array.coeffs state_array.matrix n j) j j := by
                rw [h_array_step_eq_j]
              rw [h_write_eq]
              have hrow : j < state_array.coeffs.size := by
                rw [h_coeffs_size]; exact hjn
              have hcol : j < state_array.coeffs[j]!.size := by
                rw [h_coeffs_rows_size j hjn]; exact hjn
              rw [getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol]
              -- Goal: getArrayEntry state_array.matrix j j = state_matrix.matrix[jFin][jFin]
              rw [getArrayEntry_eq_rowsToMatrix state_array.matrix jFin jFin]
              rw [h_matrix_eq]
            · have hj_lt : j < state_matrix.step := Nat.lt_of_le_of_ne hj_le hj_eq
              rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _
                (show j ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_processed j hj_lt hjn
          have h_coeffs_unwritten_new :
              ∀ j (_hjs : new_matrix.step ≤ j) (_hjn : j < n),
                getArrayEntry new_array.coeffs j j = 0 := by
            intro j hjs hjn
            show getArrayEntry (writeScaledColumn _ _ _ _) j j = 0
            have hj_gt : state_matrix.step < j := hjs
            rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _
              (show j ≠ state_array.step by rw [h_step_eq]; omega)]
            exact h_coeffs_unwritten j (Nat.le_of_lt hj_gt) hjn
          have h_fuel_new : i.val < new_matrix.step + fuel' ∨ i.val < new_matrix.step := by
            show i.val < state_matrix.step + 1 + fuel' ∨ i.val < state_matrix.step + 1
            rcases h_fuel with hor1 | hor2
            · left; omega
            · right; omega
          exact ih h_step_new h_matrix_new h_prev_new h_no_sing_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_coeffs_processed_new h_coeffs_unwritten_new h_fuel_new
      · -- Subcase B: state_matrix.step + 1 ≥ n.
        rw [Matrix.noPivotLoop_done fuel' state_matrix hDone]
        left
        refine ⟨h_no_sing, ?_⟩
        by_cases hArrayStep : state_array.step < n
        · have hArrayNext : ¬ state_array.step + 1 < n := h_step_eq ▸ hDone
          rw [scaledCoeffArrayLoop_last_step fuel' state_array hArrayStep hArrayNext]
          by_cases h_ieq : i.val = state_matrix.step
          · have h_array_step_eq_i : state_array.step = i.val := by
              rw [h_step_eq]; exact h_ieq.symm
            change getArrayEntry (writeScaledColumn _ _ _ _) i.val i.val = _
            have h_rewrite_step :
                getArrayEntry
                    (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                  getArrayEntry
                    (writeScaledColumn state_array.coeffs state_array.matrix n i.val) i.val i.val := by
              rw [h_array_step_eq_i]
            rw [h_rewrite_step]
            have hrow : i.val < state_array.coeffs.size := by
              rw [h_coeffs_size]; exact i.isLt
            have hcol : i.val < state_array.coeffs[i.val]!.size := by
              rw [h_coeffs_rows_size i.val i.isLt]; exact i.isLt
            rw [getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol]
            rw [getArrayEntry_eq_rowsToMatrix state_array.matrix i i]
            rw [h_matrix_eq]
          · by_cases h_ilt : i.val < state_matrix.step
            · change getArrayEntry (writeScaledColumn _ _ _ _) i.val i.val = _
              rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _
                (show i.val ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_processed i.val h_ilt i.isLt
            · have h_ilt : state_matrix.step ≤ i.val := Nat.le_of_not_lt h_ilt
              have h_igt : state_matrix.step < i.val :=
                Nat.lt_of_le_of_ne h_ilt fun h => h_ieq h.symm
              have hDone : ¬ state_matrix.step + 1 < n := hDone
              omega
        · rw [scaledCoeffArrayLoop_id_at_done (fuel' + 1) state_array hArrayStep]
          have hArrayStep' : n ≤ state_array.step := Nat.le_of_not_lt hArrayStep
          have h_ilt : i.val < state_matrix.step := by
            rw [← h_step_eq]; exact Nat.lt_of_lt_of_le i.isLt hArrayStep'
          exact h_coeffs_processed i.val h_ilt i.isLt
/-- The no-pivot Bareiss pass over the full Gram matrix records the same
leading-prefix determinant as the public `gramDet` API at every vector slot. -/
private theorem gramDetVecEntry_eq_leadingPrefix_bareiss
    (b : Matrix Int n m) (hquot : StepWitness b) (r : Nat) (hr : r < n) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ =
      (Matrix.bareiss
        (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
          (Nat.succ_le_of_lt hr))).toNat := by
  let GM := Matrix.gramMatrix b
  let init := Matrix.noPivotInitialState GM
  let data := Matrix.bareissNoPivotData GM
  let i : Fin n := ⟨r, hr⟩
  by_cases h_prefix :
      (Matrix.noPivotLoop r init).singularStep = none
  · have hdiag :=
      bareissNoPivotData_diag_eq_leadingPrefix_bareiss_of_prefix_nonsingular
        (b := b) r hr (by simpa [GM, init] using h_prefix)
    have h_step_r : (Matrix.noPivotLoop r init).step = r := by
      have h_room : init.step + r + 1 ≤ n := by
        simp [init, Matrix.noPivotInitialState]
        omega
      have h := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        r init rfl h_room h_prefix
      simpa [init, Matrix.noPivotInitialState] using h
    have h_entry_diag :
        gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (data.matrix[i][i]).toNat := by
      have h_split : r + (n - r) = n := by omega
      have h_full :
          Matrix.noPivotLoop n init =
            Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r init) := by
        simpa [h_split] using Matrix.noPivotLoop_add r (n - r) init
      rcases noPivotLoop_singular_inv (n := n) (n - r)
          (Matrix.noPivotLoop r init) h_prefix with h_none | h_sing
      · have hdata : data.singularStep = none := by
          simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full] using h_none
        simp [gramDetVecEntry, data, hdata, i]
        rfl
      · rcases h_sing with ⟨k, h_sing_full, h_step_full, h_zero_full, _hk_bound⟩
        have hdata : data.singularStep = some k.val := by
          simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full] using h_sing_full
        have hmono := noPivotLoop_step_monotone (n - r) (Matrix.noPivotLoop r init)
        have hr_le_k : r ≤ k.val := by
          rw [h_step_r, h_step_full] at hmono
          exact hmono
        by_cases hkr : k.val = r
        · have hlt : k.val < r + 1 := by omega
          have hdata_matrix :
              data.matrix[i][i] =
                (Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r init)).matrix[i][i] := by
            simp [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full]
          have hzero_i : data.matrix[i][i] = 0 := by
            have hi_eq : i = k := Fin.ext hkr.symm
            rw [hdata_matrix]
            simpa [hi_eq] using h_zero_full
          simp [gramDetVecEntry, data, hdata, i, hlt]
          simpa [data, i] using (congrArg Int.toNat hzero_i).symm
        · have hlt : ¬ k.val < r + 1 := by omega
          simp [gramDetVecEntry, data, hdata, i, hlt]
          rfl
    calc
      gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
          ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (data.matrix[i][i]).toNat := by
            simpa [data, GM, i] using h_entry_diag
      _ = (Matrix.bareiss
            (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
              (Nat.succ_le_of_lt hr))).toNat := by
            exact congrArg Int.toNat (by simpa [data, GM, i] using hdiag)
  · rcases noPivotLoop_singular_inv (n := n) r init rfl with h_none | h_sing
    · exact False.elim (h_prefix h_none)
    · rcases h_sing with ⟨k, h_sing_r, h_step_r, h_zero_r, h_klt⟩
      have hsr : k.val < r + 1 := by
        have h := noPivotLoop_singularStep_lt (n := n) r init rfl k.val h_sing_r
        simp [init, Matrix.noPivotInitialState] at h
        omega
      have h_full_eq :
          Matrix.noPivotLoop n init = Matrix.noPivotLoop r init := by
        have h_split : n = r + (n - r) := by omega
        have hext :=
          noPivotLoop_extends_singularStep init r (n - r) k
            h_sing_r h_step_r h_zero_r h_klt
        exact (congrArg (fun fuel => Matrix.noPivotLoop fuel init) h_split).trans hext
      have hdata : data.singularStep = some k.val := by
        simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full_eq] using h_sing_r
      have hleft :
          gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 := by
        simp [gramDetVecEntry, data, hdata, hsr]
      have hright :
          (Matrix.bareiss
            (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
              (Nat.succ_le_of_lt hr))).toNat = 0 :=
        leadingPrefix_gram_bareiss_toNat_eq_zero
          (b := b) r hr hquot k.val (by simpa [GM, init] using h_sing_r)
      rw [hright]
      simpa [data, GM] using hleft

/-- The no-pivot Bareiss pass over the full Gram matrix records the same
leading-prefix determinant as the public `gramDet` API at every vector slot. -/
theorem gramDetVecEntry_eq_gramDet
    (b : Matrix Int n m) (hquot : StepWitness b) (k : Nat) (hk : k ≤ n) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨k, Nat.lt_succ_of_le hk⟩ =
      gramDet b k hk := by
  cases k with
  | zero =>
      rw [show hk = Nat.zero_le n from Subsingleton.elim _ _]
      rfl
  | succ r =>
      have hr : r < n := Nat.lt_of_succ_le hk
      calc
        gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
            ⟨r + 1, Nat.lt_succ_of_le hk⟩ =
          gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
            ⟨r + 1, Nat.succ_lt_succ hr⟩ := by
              rfl
        _ = (Matrix.bareiss
              (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
                (Nat.succ_le_of_lt hr))).toNat :=
              gramDetVecEntry_eq_leadingPrefix_bareiss (b := b) hquot r hr
        _ = gramDet b (r + 1) hk := by
              simp [gramDet, GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram]


/-- The scaled-coefficient array loop writes the same diagonal determinant
values as `gramDetVecEntry`, including the zero tail after an early singular
no-pivot Bareiss step. -/
private theorem scaledCoeffRows_diag_toNat_eq_gramDetVecEntry
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    (getArrayEntry (scaledCoeffRows b) i i).toNat =
      gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨i + 1, Nat.succ_lt_succ hi⟩ := by
  let iFin : Fin n := ⟨i, hi⟩
  have hdiag :=
    scaledCoeffArrayLoop_diag_matches
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (rowsToMatrix_gramRows b) (by rfl) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      (by
        intro j hjs _hjn
        simp [Matrix.noPivotInitialState] at hjs)
      (by
        intro j _hjs _hjn
        exact getArrayEntry_zeroRows n j j)
      n iFin (by
        left
        simp [Matrix.noPivotInitialState, iFin, hi])
  show (getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i).toNat =
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
      ⟨i + 1, Nat.succ_lt_succ hi⟩
  rcases hdiag with ⟨h_sing, h_eq⟩ | ⟨s, h_sing, h_cases⟩
  · simp only [Matrix.bareissNoPivotData, gramDetVecEntry, Matrix.finish,
      bareissDiagNat, h_sing]
    exact congrArg Int.toNat h_eq
  · simp only [Matrix.bareissNoPivotData, gramDetVecEntry, Matrix.finish,
      bareissDiagNat, h_sing]
    rcases h_cases with ⟨hsi, h_zero⟩ | ⟨his, h_eq⟩
    · have hsi' : s ≤ i := by
        simpa [iFin] using hsi
      have hs_lt : s < i + 1 := by omega
      rw [if_pos hs_lt]
      exact congrArg Int.toNat h_zero
    · have his' : i < s := by
        simpa [iFin] using his
      have hs_not_lt : ¬ s < i + 1 := by omega
      rw [if_neg hs_not_lt]
      exact congrArg Int.toNat h_eq

/-- The scaled-coefficient loop stores the next leading Gram determinant on
the diagonal, at the executable Nat boundary. -/
private theorem scaledCoeffRows_diag_toNat_eq_gramDet
    (b : Matrix Int n m) (hquot : StepWitness b) (i : Nat) (hi : i < n) :
    (getArrayEntry (scaledCoeffRows b) i i).toNat =
      gramDet b (i + 1) (Nat.succ_le_of_lt hi) := by
  rw [scaledCoeffRows_diag_toNat_eq_gramDetVecEntry (b := b) i hi]
  rw [gramDetVecEntry_eq_gramDet (b := b) hquot (i + 1) (Nat.succ_le_of_lt hi)]

/-- Signed leading-prefix diagonal information from the executable
scaled-coefficient loop: the diagonal slot is either the zero tail after an
early singular no-pivot step, or the Bareiss determinant of the matching
leading Gram prefix. -/
private theorem scaledCoeffRows_diag_eq_zero_or_eq_leadingPrefix_bareiss
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    getArrayEntry (scaledCoeffRows b) i i = 0 ∨
      getArrayEntry (scaledCoeffRows b) i i =
        Matrix.bareiss
          (Matrix.leadingPrefix (Matrix.gramMatrix b) (i + 1)
            (Nat.succ_le_of_lt hi)) := by
  let iFin : Fin n := ⟨i, hi⟩
  have hdiag :=
    scaledCoeffArrayLoop_diag_matches
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (rowsToMatrix_gramRows b) (by rfl) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      (by
        intro j hjs _hjn
        simp [Matrix.noPivotInitialState] at hjs)
      (by
        intro j _hjs _hjn
        exact getArrayEntry_zeroRows n j j)
      n iFin (by
        left
        simp [Matrix.noPivotInitialState, iFin, hi])
  show getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i = 0 ∨
    getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i =
        Matrix.bareiss
          (Matrix.leadingPrefix (Matrix.gramMatrix b) (i + 1)
            (Nat.succ_le_of_lt hi))
  rcases hdiag with ⟨h_sing, h_eq⟩ | ⟨s, h_sing, h_cases⟩
  · right
    have h_final :
        (Matrix.noPivotLoop (i + (n - i))
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
      have h_split : i + (n - i) = n := by omega
      simpa [h_split] using h_sing
    have h_prefix :
        (Matrix.noPivotLoop i
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none :=
      noPivotLoop_prefix_none_of_final_none i (n - i)
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_final
    have h_leading :=
      bareissNoPivotData_diag_eq_leadingPrefix_bareiss_of_prefix_nonsingular
        (b := b) i hi h_prefix
    have h_eq_noPivot :
        getArrayEntry
          (scaledCoeffArrayLoop n n
            { step := 0
              matrix := gramRows b
              coeffs := zeroRows n
              prevPivot := 1 }).coeffs i i =
          (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[iFin][iFin] := by
      simpa [Matrix.bareissNoPivotData, Matrix.finish, iFin] using h_eq
    exact h_eq_noPivot.trans h_leading
  · rcases h_cases with ⟨_hsi, h_zero⟩ | ⟨his, h_eq⟩
    · left
      simpa [iFin] using h_zero
    · right
      have h_final :
          (Matrix.noPivotLoop (i + (n - i))
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s := by
        have h_split : i + (n - i) = n := by omega
        simpa [h_split] using h_sing
      have h_after : (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + i ≤ s := by
        simp [Matrix.noPivotInitialState]
        have : i < s := by
          simpa [iFin] using his
        omega
      have h_prefix :
          (Matrix.noPivotLoop i
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none :=
        noPivotLoop_prefix_none_of_final_singular_after i (n - i)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_final h_after
      have h_leading :=
        bareissNoPivotData_diag_eq_leadingPrefix_bareiss_of_prefix_nonsingular
          (b := b) i hi h_prefix
      have h_eq_noPivot :
          getArrayEntry
            (scaledCoeffArrayLoop n n
              { step := 0
                matrix := gramRows b
                coeffs := zeroRows n
                prevPivot := 1 }).coeffs i i =
            (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[iFin][iFin] := by
        simpa [Matrix.bareissNoPivotData, Matrix.finish, iFin] using h_eq
      exact h_eq_noPivot.trans h_leading

/-- The empty leading Gram determinant is `1`: the determinant of the `0 × 0`
principal Gram minor. This is the base case anchoring the `gramDetVec` diagonal
recurrence (`gramDetVec_eq_gramDet` at `k = 0`). -/
@[simp, grind =] theorem gramDet_zero (b : Matrix Int n m) :
    gramDet b 0 (Nat.zero_le n) = 1 := by
  rfl

/-- Both `scaledCoeffRows` and `scaledCoeffRowsSchur` start from `zeroRows n`
and only write strict-lower / diagonal entries; the upper-triangle slot at
`(i, j)` with `i < j` therefore retains its initial zero value, regardless of
whether `i` and `j` lie inside the array bounds. -/
private theorem getArrayEntry_scaledCoeffRows_above
    (b : Matrix Int n m) (i j : Nat) (hij : i < j) :
    getArrayEntry (scaledCoeffRows b) i j = 0 := by
  unfold scaledCoeffRows
  exact getArrayEntry_scaledCoeffArrayLoop_above n n _
    (fun i' j' hij' => getArrayEntry_zeroRows n i' j') i j hij

/-- The integral scaled Gram-Schmidt coefficient matrix is lower triangular:
every strict-upper-triangle entry (`i < j`) is zero. Callers treating
`scaledCoeffs` as a triangular factor use this to discard above-diagonal terms.
Tagged `@[grind =]` (keyed on the `entry (scaledCoeffs b) i j` term) so the
strict-upper hypothesis `i < j` is discharged by `grind`'s arithmetic when the
vanishing fact is needed. -/
@[grind =] theorem scaledCoeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  rw [scaledCoeffs_entry_eq_getArrayEntry]
  exact getArrayEntry_scaledCoeffRowsSchur_upper b i j hij

private theorem foldl_add_eq_acc_rat_int {α : Type u}
    (xs : List α) (f : α → Rat) (acc : Rat)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hacc : acc + (0 : Rat) = acc := by grind
      rw [hacc]
      exact ih acc hxs

private theorem foldl_finRange_eq_prefix_of_zero_above_from
    {n : Nat} (k : Fin n) (f : Fin n → Rat) (acc : Rat)
    (hzero : ∀ j : Fin n, k.val < j.val → f j = 0) :
    (List.finRange n).foldl (fun acc j => acc + f j) acc =
      (List.finRange (k.val + 1)).foldl
        (fun acc j =>
          acc + f ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩) acc := by
  induction n generalizing acc with
  | zero =>
      exact Fin.elim0 k
  | succ n ih =>
      cases k using Fin.cases with
      | zero =>
          have htail : ∀ j ∈ (List.finRange n).map Fin.succ, f j = 0 := by
            intro j hj
            rcases List.mem_map.mp hj with ⟨i, _hi, rfl⟩
            exact hzero (Fin.succ i) (Nat.succ_pos i.val)
          have htailFold :
              ((List.finRange n).map Fin.succ).foldl (fun acc j => acc + f j)
                  (acc + f 0) = acc + f 0 :=
            foldl_add_eq_acc_rat_int ((List.finRange n).map Fin.succ) (fun j => f j)
              (acc + f 0) htail
          simpa [List.finRange_succ] using htailFold
      | succ k =>
          have hzero_tail : ∀ j : Fin n, k.val < j.val → f (Fin.succ j) = 0 := by
            intro j hj
            exact hzero (Fin.succ j) (Nat.succ_lt_succ hj)
          have htail := ih k (fun j => f (Fin.succ j)) (acc + f 0) hzero_tail
          have htail' :
              ((List.finRange n).map Fin.succ).foldl (fun acc j => acc + f j)
                  (acc + f 0) =
                ((List.finRange (k.val + 1)).map Fin.succ).foldl
                  (fun acc j =>
                    acc + f ⟨j.val,
                      Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt (Fin.succ k).isLt)⟩)
                  (acc + f 0) := by
            simpa [List.foldl_map] using htail
          simpa [List.finRange_succ, Nat.succ_eq_add_one, Nat.add_assoc] using htail'

private theorem foldl_finRange_eq_prefix_of_zero_above
    {n : Nat} (k : Fin n) (f : Fin n → Rat)
    (hzero : ∀ j : Fin n, k.val < j.val → f j = 0) :
    (List.finRange n).foldl (fun acc j => acc + f j) 0 =
      (List.finRange (k.val + 1)).foldl
        (fun acc j =>
          acc + f ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩) 0 :=
  foldl_finRange_eq_prefix_of_zero_above_from k f 0 hzero

/-- A `List.finRange (k + 1)` fold whose addend vanishes on every strict
predecessor of `k` reduces to the contribution at the last index. -/
private theorem foldl_finRange_succ_eq_last_of_zero_below
    (k : Nat) (f : Fin (k + 1) → Rat) (acc : Rat)
    (hzero : ∀ j : Fin (k + 1), j.val < k → f j = 0) :
    (List.finRange (k + 1)).foldl (fun acc j => acc + f j) acc =
      acc + f ⟨k, Nat.lt_succ_self k⟩ := by
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  have hprefix :
      (List.finRange k).foldl
          (fun acc i => acc + f (Fin.castSucc i)) acc = acc := by
    refine foldl_add_eq_acc_rat_int (List.finRange k)
      (fun i => f (Fin.castSucc i)) acc ?_
    intro i _hi
    apply hzero
    change i.val < k
    exact i.isLt
  rw [hprefix]
  show acc + f (Fin.last k) = acc + f ⟨k, Nat.lt_succ_self k⟩
  rfl

/-- The `k`-th entry of the row combination of the Gram-Schmidt coefficient
matrix with a cast integer coefficient vector, when all later integer
coefficients vanish, equals the cast `k`-th coefficient.

This is the top Gram-Schmidt coordinate specialization consumed by the lattice
norm lower bound: rows below `k` contribute zero by upper-triangularity,
row `k` contributes one by the diagonal lemma, and rows above `k` contribute
zero because the corresponding integer coefficient vanishes. -/
theorem rowCombination_coeffs_apply_eq_of_zero_above
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero_above : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    (Matrix.rowCombination (coeffs b)
        (Vector.map (fun x : Int => (x : Rat)) c))[k]
      = ((c[k] : Int) : Rat) := by
  let castc : Vector Rat n := Vector.map (fun x : Int => (x : Rat)) c
  have hcastc_get : ∀ i : Fin n, castc[i] = ((c[i] : Int) : Rat) := by
    intro i
    show (Vector.map (fun x : Int => (x : Rat)) c)[i.val]'i.isLt
        = ((c[i.val]'i.isLt : Int) : Rat)
    rw [Vector.getElem_map]
  -- Embed indices from the truncated prefix back into `Fin n`.
  let liftj : Fin (k.val + 1) → Fin n := fun j =>
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
  rw [show
      (Matrix.rowCombination (coeffs b)
          (Vector.map (fun x : Int => (x : Rat)) c))[k]
        = (Matrix.rowCombination (coeffs b) castc)[k] from rfl]
  -- Step 1: rewrite the row-combination entry as a fold over the `k`-th column.
  have hcol :
      (Matrix.rowCombination (coeffs b) castc)[k]
        = (List.finRange n).foldl
            (fun acc i => acc + (coeffs b)[i][k] * castc[i]) 0 := by
    show ((coeffs b).transpose * castc)[k] = _
    rw [Matrix.mulVec_getElem]
    show Matrix.dot (((coeffs b).transpose).row k) castc = _
    show (List.finRange n).foldl
        (fun acc i =>
          acc + (((coeffs b).transpose).row k)[i] * castc[i]) 0 = _
    simp only [Matrix.row_getElem, Matrix.transpose_getElem]
  rw [hcol]
  -- Step 2: drop the tail above `k` via the zero-above truncation helper.
  let f : Fin n → Rat := fun i => (coeffs b)[i][k] * castc[i]
  have habove : ∀ j : Fin n, k.val < j.val → f j = 0 := by
    intro j hj
    show (coeffs b)[j][k] * castc[j] = 0
    rw [hcastc_get j]
    have hcj : c[j] = 0 := hzero_above j hj
    rw [hcj]
    show (coeffs b)[j][k] * (((0 : Int) : Rat)) = 0
    grind
  have htrunc :
      (List.finRange n).foldl (fun acc j => acc + f j) 0
        = (List.finRange (k.val + 1)).foldl
            (fun acc j => acc + f (liftj j)) 0 :=
    foldl_finRange_eq_prefix_of_zero_above k f habove
  show (List.finRange n).foldl (fun acc j => acc + f j) 0
      = ((c[k] : Int) : Rat)
  rw [htrunc]
  -- Step 3: isolate the contribution at `j = k`, using `coeffs_upper` for the
  -- entries strictly below `k`.
  let g : Fin (k.val + 1) → Rat := fun j => f (liftj j)
  have hbelow : ∀ j : Fin (k.val + 1), j.val < k.val → g j = 0 := by
    intro j hj
    show (coeffs b)[liftj j][k] * castc[liftj j] = 0
    have hentry :
        GramSchmidt.entry (coeffs b) (liftj j) k = 0 := by
      have h := coeffs_upper b j.val k.val
        (Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)) k.isLt hj
      have hkeq : (⟨k.val, k.isLt⟩ : Fin n) = k := Fin.ext rfl
      change GramSchmidt.entry (coeffs b) (liftj j) ⟨k.val, k.isLt⟩ = 0 at h
      rwa [hkeq] at h
    have : (coeffs b)[liftj j][k] = 0 := hentry
    rw [this]
    grind
  have hisolate :
      (List.finRange (k.val + 1)).foldl (fun acc j => acc + g j) 0
        = 0 + g ⟨k.val, Nat.lt_succ_self k.val⟩ :=
    foldl_finRange_succ_eq_last_of_zero_below k.val g 0 hbelow
  rw [hisolate]
  -- Step 4: evaluate `g` at the last index using `coeffs_diag`.
  change 0 + (coeffs b)[k][k] * castc[k] = ((c[k] : Int) : Rat)
  rw [hcastc_get k]
  have hdiag :
      GramSchmidt.entry (coeffs b) k k = 1 := by
    have h := coeffs_diag b k.val k.isLt
    have hkeq : (⟨k.val, k.isLt⟩ : Fin n) = k := Fin.ext rfl
    rwa [hkeq] at h
  have hkk : (coeffs b)[k][k] = 1 := hdiag
  rw [hkk]
  grind

end GramSchmidt.Int
end Hex
