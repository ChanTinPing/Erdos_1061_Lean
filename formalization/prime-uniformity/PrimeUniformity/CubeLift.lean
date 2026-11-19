module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

public section

namespace PrimeUniformity

open scoped BigOperators

/-- A bounded representative of a modular cube vertex is the corresponding
integer vertex once the modulus exceeds the possible difference. -/
theorem cube_vertex_eq_of_modEq {ι : Type*} (I : Finset ι) {p : ℕ} {X b w : ℤ}
    (s : ι → ℤ) (hb : |b| ≤ X) (hw : |w| ≤ X) (hs : ∀ i ∈ I, |s i| ≤ X)
    (hp : (2 * (I.card : ℤ) + 2) * X < (p : ℤ))
    (hmod : (w : ZMod p) = (b : ZMod p) + (∑ i ∈ I, ((s i : ZMod p) - (b : ZMod p)))) :
    w = b + (∑ i ∈ I, (s i - b)) := by
  have hsum : |∑ i ∈ I, (s i - b)| ≤ (I.card : ℤ) * (2 * X) := by
    calc
      _ ≤ ∑ i ∈ I, |s i - b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ I, 2 * X := by
        apply Finset.sum_le_sum
        intro i hi
        exact (abs_sub _ _).trans ((add_le_add (hs i hi) hb).trans_eq (by ring))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hbound : |w - (b + (∑ i ∈ I, (s i - b)))| ≤ (2 * (I.card : ℤ) + 2) * X := by
    calc
      _ ≤ |w| + |b + (∑ i ∈ I, (s i - b))| := abs_sub _ _
      _ ≤ |w| + (|b| + |∑ i ∈ I, (s i - b)|) := Int.add_le_add_left (abs_add_le _ _) _
      _ ≤ X + (X + (I.card : ℤ) * (2 * X)) := add_le_add hw (add_le_add hb hsum)
      _ = _ := by ring
  have hdvd : (p : ℤ) ∣ w - (b + (∑ i ∈ I, (s i - b))) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [Int.cast_sub, Int.cast_add, Int.cast_sum, hmod, sub_self]
  apply sub_eq_zero.mp
  by_contra hn
  exact (not_lt_of_ge (Int.le_abs_of_dvd hn hdvd)) (hbound.trans_lt hp)

/-- The side bound can use the dimension of a cube instead of the size of
the particular set of active directions. -/
theorem cube_vertex_eq_of_representatives {ι : Type*} (I : Finset ι)
    {p n : ℕ} {X b w : ℤ} (s : ι → ℤ) (base : ZMod p) (edge : ι → ZMod p)
    (hb : |b| ≤ X) (hw : |w| ≤ X) (hs : ∀ i ∈ I, |s i| ≤ X)
    (hI : I.card ≤ n) (hp : (2 * (n : ℤ) + 2) * X < (p : ℤ))
    (hbase : (b : ZMod p) = base)
    (hsingle : ∀ i ∈ I, (s i : ZMod p) = base + edge i)
    (hvertex : (w : ZMod p) = base + (∑ i ∈ I, edge i)) :
    w = b + (∑ i ∈ I, (s i - b)) := by
  have hX : 0 ≤ X := (abs_nonneg b).trans hb
  have hcard : (I.card : ℤ) ≤ (n : ℤ) := by exact_mod_cast hI
  have hfactor : 2 * (I.card : ℤ) + 2 ≤ 2 * (n : ℤ) + 2 :=
    Int.add_le_add_right (mul_le_mul_of_nonneg_left hcard (by decide)) _
  refine cube_vertex_eq_of_modEq I s hb hw hs
    ((mul_le_mul_of_nonneg_right hfactor hX).trans_lt hp) ?_
  rw [hvertex, hbase]
  refine congrArg (fun u : ZMod p => base + u) ?_
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsingle i hi]
  ring

end PrimeUniformity
