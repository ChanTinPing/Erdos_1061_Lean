module

public import PrimeUniformity.IntervalMoment
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- Every cube product admits the supremum bound with one factor per vertex. -/
theorem norm_cubeProduct_le {A : Type*} [Add A] (d : ℕ)
    (f : A → ℂ) {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B)
    (x : A) (h : Fin d → A) :
    ‖cubeProduct d f x h‖ ≤ B ^ (2 ^ d : ℕ) := by
  induction d generalizing x with
  | zero => simpa [cubeProduct] using hf x
  | succ d ih =>
    rw [cubeProduct, norm_mul, Complex.norm_conj, pow_succ (2 : ℕ), pow_mul, pow_two]
    exact mul_le_mul (ih _ _) (ih _ _) (norm_nonneg _) (pow_nonneg hB _)

/-- If the base lies outside the support its cube product is zero, so only
support size times the number of choices of the singleton endpoints matters. -/
theorem intervalCubeSum_le_support (d X : ℕ) (w : ℤ → ℝ) (S : Finset (Fin X))
    {B : ℝ} (hB : 0 ≤ B) (hw : ∀ n, ‖intervalWeight X w n‖ ≤ B)
    (hs : ∀ i ∉ S, intervalWeight X w (intervalEndpoint i) = 0) :
    intervalCubeSum d X w ≤ (S.card : ℝ) * (X : ℝ) ^ d * B ^ (2 ^ d : ℕ) := by
  classical
  let P (i : Fin X) (h : Fin d → Fin X) :=
    cubeProduct d (intervalWeight X w) (intervalEndpoint i)
      (fun j => intervalEndpoint (h j) - intervalEndpoint i)
  unfold intervalCubeSum
  change (∑ a : Fin X × (Fin d → Fin X), (P a.1 a.2).re) ≤ _
  rw [Fintype.sum_prod_type' (fun i h => (P i h).re)]
  have hz (i : Fin X) (hi : i ∉ S) (h : Fin d → Fin X) : P i h = 0 := by
    apply cubeProduct_eq_zero_of_vertex _ _ _ _ (fun _ => false)
    simpa [cubeVertex] using hs i hi
  rw [← Finset.sum_subset (s₂ := Finset.univ) (Finset.subset_univ S) (by
    intro i _ hi
    simp only [hz i hi, Complex.zero_re, Finset.sum_const_zero])]
  calc
    _ ≤ ∑ i ∈ S, ∑ _ : Fin d → Fin X, B ^ (2 ^ d : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro h _
      exact (Complex.re_le_norm _).trans (norm_cubeProduct_le d _ hB hw _ _)
    _ = _ := by simp [nsmul_eq_mul]; ring

/-- A grid of short nonnegative increments gives a uniform lower bound on
the number of admissible interval cubes. -/
theorem pow_le_intervalCubes_card (d X M : ℕ) (hMX : (d + 1) * M ≤ X) :
    M ^ (d + 1) ≤ (intervalCubes d X).card := by
  classical
  have hM : M ≤ (d + 1) * M := by
    simpa using Nat.mul_le_mul_right M (show 1 ≤ d + 1 by omega)
  let start (a : Fin M × (Fin d → Fin M)) : Fin X :=
    ⟨a.1.val, a.1.isLt.trans_le (hM.trans hMX)⟩
  let single (a : Fin M × (Fin d → Fin M)) (i : Fin d) : Fin X :=
    ⟨a.1.val + (a.2 i).val, by
      have hi := i.isLt
      have hs := Nat.mul_le_mul_right M (show 2 ≤ d + 1 by omega)
      have ha := a.1.isLt
      have hb := (a.2 i).isLt
      omega⟩
  let lift (a : Fin M × (Fin d → Fin M)) := (start a, single a)
  have hlift : Function.Injective lift := by
    intro a b hab
    have ha := congrArg (fun v : Fin X × (Fin d → Fin X) => v.1.val) hab
    change a.1.val = b.1.val at ha
    refine Prod.ext (Fin.ext ha) ?_
    funext i
    apply Fin.ext
    have h := congrArg (fun v : Fin X × (Fin d → Fin X) => (v.2 i).val) hab
    change a.1.val + (a.2 i).val = b.1.val + (b.2 i).val at h
    omega
  have hmem (a : Fin M × (Fin d → Fin M)) : lift a ∈ intervalCubes d X := by
    rw [intervalCubes, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro v
    have hstart : intervalEndpoint (start a) = (a.1.val : ℤ) + 1 := rfl
    have hstep (i : Fin d) :
        intervalEndpoint (single a i) - intervalEndpoint (start a) = ((a.2 i).val : ℤ) := by
      change ((a.1.val + (a.2 i).val : ℕ) : ℤ) + 1 - ((a.1.val : ℤ) + 1) = _
      push_cast
      ring
    simp only [lift, cubeVertex, hstep]
    rw [hstart]
    have hnonneg : 0 ≤ ∑ i : Fin d, if v i then ((a.2 i).val : ℤ) else 0 := by
      apply Finset.sum_nonneg
      intro i _
      split <;> positivity
    have hsum : (∑ i : Fin d, if v i then ((a.2 i).val : ℤ) else 0) ≤ (d : ℤ) * M := by
      calc
        _ ≤ ∑ _ : Fin d, (M : ℤ) := by
          apply Finset.sum_le_sum
          intro i _
          split
          · exact_mod_cast (a.2 i).isLt.le
          · positivity
        _ = _ := by simp
    have hb : (a.1.val : ℤ) + 1 ≤ (M : ℤ) := by
      exact_mod_cast (Nat.succ_le_of_lt a.1.isLt)
    have hMX' : ((d : ℤ) + 1) * M ≤ (X : ℤ) := by exact_mod_cast hMX
    refine ⟨by omega, ?_⟩
    calc
      _ ≤ (M : ℤ) + (d : ℤ) * M := add_le_add hb hsum
      _ = ((d : ℤ) + 1) * M := by ring
      _ ≤ _ := hMX'
  have hcard := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin M × (Fin d → Fin M))))
    lift (fun a _ => hmem a) hlift.injOn
  simpa [pow_succ, Nat.mul_comm] using hcard

/-- At fixed order the number of admissible cubes has a uniform power lower bound. -/
theorem intervalCubeSum_one_ge {d X : ℕ} (hX : 2 * (d + 1) ≤ X) :
    (X : ℝ) ^ (d + 1) ≤ (2 * ((d : ℝ) + 1)) ^ (d + 1) *
      intervalCubeSum d X (fun _ => 1) := by
  let M := X / (d + 1)
  have hMX : (d + 1) * M ≤ X := Nat.mul_div_le X (d + 1)
  have hM₁ : 1 ≤ M := (Nat.le_div_iff_mul_le (Nat.succ_pos d)).mpr (by omega)
  have hrem : X % (d + 1) ≤ (d + 1) * M :=
    (Nat.mod_lt X (Nat.succ_pos d)).le.trans (by
      simpa using Nat.mul_le_mul_left (d + 1) hM₁)
  have hdiv := Nat.div_add_mod X (d + 1)
  change (d + 1) * M + X % (d + 1) = X at hdiv
  have hbound : (X : ℝ) ≤ (2 * ((d : ℝ) + 1)) * M := by
    have h := calc
      X = (d + 1) * M + X % (d + 1) := hdiv.symm
      _ ≤ (d + 1) * M + (d + 1) * M := Nat.add_le_add_left hrem _
      _ = 2 * (d + 1) * M := by ring
    exact_mod_cast h
  have hcard : (M : ℝ) ^ (d + 1) ≤ intervalCubeSum d X (fun _ => 1) := by
    rw [intervalCubeSum_one_eq_card]
    exact_mod_cast pow_le_intervalCubes_card d X M hMX
  calc
    _ ≤ ((2 * ((d : ℝ) + 1)) * M) ^ (d + 1) := pow_le_pow_left₀ (by positivity) hbound _
    _ = (2 * ((d : ℝ) + 1)) ^ (d + 1) * (M : ℝ) ^ (d + 1) := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard (by positivity)

end PrimeUniformity
