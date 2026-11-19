module

public import Jsp000881.Coefficients
import all Jsp000881.Coefficients
public import Jsp000881.SieveBounds
import all Jsp000881.SieveBounds
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# A uniform lower bound for the truncated local-factor product

The tail proof is finite. A telescoping upper bound on the sum of the
deficits and the first-order Bonferroni product inequality give a lower
bound independent of the cutoff.
-/

public section

namespace Jsp000881

open scoped BigOperators

private theorem one_sub_sum_le_prod_one_sub (s : Finset ℕ) (e : ℕ → ℝ)
    (he : ∀ p ∈ s, 0 ≤ e p ∧ e p ≤ 1) :
    1 - (∑ p ∈ s, e p) ≤ ∏ p ∈ s, (1 - e p) := by
  classical
  revert he
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert p s hp ih =>
    intro he
    have hep := he p (Finset.mem_insert_self p s)
    have hes : ∀ q ∈ s, 0 ≤ e q ∧ e q ≤ 1 :=
      fun q hq => he q (Finset.mem_insert_of_mem hq)
    have hsum : 0 ≤ ∑ q ∈ s, e q := Finset.sum_nonneg fun q hq => (hes q hq).1
    rw [Finset.sum_insert hp, Finset.prod_insert hp]
    calc
      _ ≤ (1 - e p) * (1 - ∑ q ∈ s, e q) := by
        nlinarith only [mul_nonneg hep.1 hsum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (ih hes) (sub_nonneg.mpr hep.2)

/-- A fixed initial envelope and square-summable tail deficits bound all
finite products below by a common positive constant. -/
theorem uniform_finite_factor_product_lower_bound (C : ℝ) (M : ℕ)
    (hC : 0 ≤ C) (hM : 0 < M) (hCM : 2 * C ≤ (M : ℝ)) (envelope : ℕ → ℝ)
    (he : ∀ p ≤ M, 0 < envelope p ∧ envelope p ≤ 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ (f : ℕ → ℝ) (s : Finset ℕ),
      (∀ p ∈ s, p ≤ M → envelope p ≤ f p) →
      (∀ p ∈ s, M < p → 1 - C / (p : ℝ) ^ 2 ≤ f p) →
      d ≤ ∏ p ∈ s, f p := by
  classical
  let initial := Finset.range (M + 1)
  have hpositive : 0 < ∏ p ∈ initial, envelope p :=
    Finset.prod_pos fun p hp => (he p (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))).1
  refine ⟨(∏ p ∈ initial, envelope p) / 2, div_pos hpositive (by norm_num), ?_⟩
  intro f s hsmall hlarge
  let small := s.filter fun p => p ≤ M
  let large := s.filter fun p => M < p
  have hsplit : small ∪ large = s := by
    ext p
    by_cases hp : p ≤ M
    · simp [small, large, hp, not_lt_of_ge hp]
    · simp [small, large, hp, lt_of_not_ge hp]
  have hdis : Disjoint small large := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge (Finset.mem_filter.mp hp).2) (Finset.mem_filter.mp hq).2
  have hsmall' : (∏ p ∈ initial, envelope p) ≤ ∏ p ∈ small, f p := by
    have hsub : small ⊆ initial := by
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_filter.mp hp).2)
    calc
      _ ≤ ∏ p ∈ small, envelope p := by
        first
        | apply Finset.prod_le_prod_of_subset_of_le_one₀ hsub
        | apply Finset.prod_le_prod_of_subset_of_le_one hsub
        · intro p hp
          exact (he p (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))).1.le
        · intro p hp _
          exact (he p (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))).2
      _ ≤ _ := by
        first
        | apply Finset.prod_le_prod₀
        | apply Finset.prod_le_prod
        · intro p hp
          exact (he p (Finset.mem_filter.mp hp).2).1.le
        · intro p hp
          exact hsmall p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  let deficit := fun p : ℕ => C / (p : ℝ) ^ 2
  have hsum : (∑ p ∈ large, deficit p) ≤ 1 / 2 := by
    have hMp : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    calc
      _ = C * (∑ p ∈ large, (1 : ℝ) / (p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        simp only [deficit, div_eq_mul_inv, one_mul]
      _ ≤ C * (1 / (M : ℝ)) := mul_le_mul_of_nonneg_left
        (sum_inverse_squares_tail_le M hM large (fun _ hp => (Finset.mem_filter.mp hp).2)) hC
      _ = C / (M : ℝ) := by simp only [div_eq_mul_inv, one_mul]
      _ ≤ _ := (div_le_iff₀ hMp).mpr (by linarith only [hCM])
  have hnonneg (p : ℕ) : 0 ≤ deficit p := div_nonneg hC (sq_nonneg _)
  have hunit : ∀ p ∈ large, 0 ≤ deficit p ∧ deficit p ≤ 1 := by
    intro p hp
    exact ⟨hnonneg p,
      ((Finset.single_le_sum (fun q _ => hnonneg q) hp).trans hsum).trans (by norm_num)⟩
  have hlarge' : (1 : ℝ) / 2 ≤ ∏ p ∈ large, f p := by
    calc
      _ ≤ 1 - (∑ p ∈ large, deficit p) := by linarith only [hsum]
      _ ≤ ∏ p ∈ large, (1 - deficit p) := one_sub_sum_le_prod_one_sub large deficit hunit
      _ ≤ _ := by
        first
        | apply Finset.prod_le_prod₀
        | apply Finset.prod_le_prod
        · intro p hp
          exact sub_nonneg.mpr (hunit p hp).2
        · intro p hp
          exact hlarge p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  calc
    _ = (∏ p ∈ initial, envelope p) * ((1 : ℝ) / 2) := by ring
    _ ≤ (∏ p ∈ small, f p) * (∏ p ∈ large, f p) :=
      mul_le_mul hsmall' hlarge' (by norm_num) (hpositive.le.trans hsmall')
    _ = _ := by rw [← Finset.prod_union hdis, hsplit]

/-- The affine rows in the original lattice coordinates, reduced modulo p. -/
def integralRowMod (θ : PlaneIndex) (p : ℕ) (i : Fin 6) : Plane.AffineRow (ZMod p) :=
  let row := integralRow θ i
  ⟨(row.constant : ZMod p), (row.left : ZMod p), (row.right : ZMod p)⟩

theorem integralRowMod_eval_cast (θ : PlaneIndex) (p : ℕ) (nm : ℤ × ℤ) (i : Fin 6) :
    (integralRowMod θ p i).eval (nm.1 : ZMod p) (nm.2 : ZMod p) =
      ((sextupleOn θ nm).coord i : ZMod p) := by
  calc
    _ = ((integralRow θ i).eval nm.1 nm.2 : ZMod p) := by
      simp only [integralRowMod, Plane.AffineRow.eval, Int.cast_add, Int.cast_mul]
    _ = _ := by rw [integralRow_eval]

/-- The residue pairs in the original lattice coordinates for which none
of the six values is zero modulo p. -/
noncomputable def goodLatticeResiduePairs (θ : PlaneIndex) (p : ℕ) [Fact p.Prime] :
    Finset (ZMod p × ZMod p) := by
  classical
  exact Finset.univ.filter fun nm => ∀ i, (integralRowMod θ p i).eval nm.1 nm.2 ≠ 0

private theorem goodLatticeResiduePairs_nonempty {θ : PlaneIndex} {p : ℕ} [Fact p.Prime]
    (hθ : LocallyAdmissible θ) : (goodLatticeResiduePairs θ p).Nonempty := by
  classical
  obtain ⟨nm, hnm⟩ := hθ p Fact.out
  refine ⟨((nm.1 : ZMod p), (nm.2 : ZMod p)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro i hi
  exact hnm i ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ((integralRowMod_eval_cast θ p nm i).symm.trans hi))

theorem card_goodLatticeResiduePairs_ge {θ : PlaneIndex} {p : ℕ} [Fact p.Prime]
    (hθ : LocallyAdmissible θ) : p * p - 6 * p ≤ (goodLatticeResiduePairs θ p).card := by
  classical
  obtain ⟨u, hu⟩ := goodLatticeResiduePairs_nonempty (p := p) hθ
  have hu' : ∀ i, (integralRowMod θ p i).eval u.1 u.2 ≠ 0 := (Finset.mem_filter.mp hu).2
  let zeros := fun i : Fin 6 => (integralRowMod θ p i).zeros
  let bad := (Finset.univ : Finset (Fin 6)).biUnion zeros
  have hbad : bad.card ≤ 6 * p := by
    have hcard := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 6)) zeros p
      (fun i _ => ((integralRowMod θ p i).card_zeros_le
        (fun h => hu' i (h u.1 u.2))).trans_eq (ZMod.card p))
    simpa [bad] using hcard
  have hmem (nm : ZMod p × ZMod p) : nm ∈ bad ↔ ∃ i, (integralRowMod θ p i).eval nm.1 nm.2 = 0 := by
    simp [bad, zeros, Plane.AffineRow.zeros]
  have he : goodLatticeResiduePairs θ p = Finset.univ \ bad := by
    ext nm
    simp only [goodLatticeResiduePairs, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and, hmem]
    exact ⟨fun h ⟨i, hi⟩ => h i hi, fun h i hi => h ⟨i, hi⟩⟩
  rw [he, Finset.card_univ_sdiff, Fintype.card_prod, ZMod.card p]
  exact Nat.sub_le_sub_left hbad _

/-- The normalized local factor for the six forms. Nonprime indices are
assigned the neutral value one. -/
noncomputable def residueFactor (θ : PlaneIndex) (p : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    ((goodLatticeResiduePairs θ p).card : ℝ) / (p : ℝ) ^ 2 / (1 - 1 / (p : ℝ)) ^ 6
  else 1

theorem residueFactor_eq_of_prime (θ : PlaneIndex) (p : ℕ) [Fact p.Prime] :
    residueFactor θ p =
      ((goodLatticeResiduePairs θ p).card : ℝ) / (p : ℝ) ^ 2 / (1 - 1 / (p : ℝ)) ^ 6 := by
  unfold residueFactor
  rw [dif_pos (Fact.out : p.Prime)]

private theorem residueDenominator_bounds {p : ℕ} (hp : p.Prime) :
    0 < (1 - 1 / (p : ℝ)) ^ 6 ∧ (1 - 1 / (p : ℝ)) ^ 6 ≤ 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpn : 1 < p := lt_of_lt_of_le (by decide) hp.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpn
  have hd0 : 0 < 1 - 1 / (p : ℝ) := sub_pos.mpr ((div_lt_iff₀ hp0).mpr (by simpa using hp1))
  have hd1 : 1 - 1 / (p : ℝ) ≤ 1 := sub_le_self _ (div_nonneg (by norm_num) hp0.le)
  exact ⟨pow_pos hd0 6, pow_le_one₀ hd0.le hd1⟩

theorem residueFactor_ge_inverse_square {θ : PlaneIndex} {p : ℕ} [Fact p.Prime]
    (hθ : LocallyAdmissible θ) : 1 / (p : ℝ) ^ 2 ≤ residueFactor θ p := by
  have hp : p.Prime := Fact.out
  have hcard : (1 : ℝ) ≤ ((goodLatticeResiduePairs θ p).card : ℝ) := by
    exact_mod_cast (show 1 ≤ (goodLatticeResiduePairs θ p).card from
      Finset.card_pos.mpr (goodLatticeResiduePairs_nonempty hθ))
  obtain ⟨hd0, hd1⟩ := residueDenominator_bounds hp
  rw [residueFactor_eq_of_prime]
  calc
    _ ≤ ((goodLatticeResiduePairs θ p).card : ℝ) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcard (sq_nonneg _)
    _ ≤ _ := (le_div_iff₀ hd0).mpr
      (mul_le_of_le_one_right (div_nonneg (by positivity) (sq_nonneg _)) hd1)

/-- A quadratic lower bound for the normalized factor from the six-line union bound. -/
private theorem normalized_six_ge {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 13) :
    1 - 30 * x ^ 2 ≤ (1 - 6 * x) / (1 - x) ^ 6 := by
  have hx1 : x ≤ 1 := by linarith only [hx]
  have hx3 : x ^ 3 ≤ 1 := pow_le_one₀ hx0 hx1
  have hrest : -20 + 15 * x - 6 * x ^ 2 + x ^ 3 ≤ 0 :=
    by linarith only [hx1, hx3, sq_nonneg x]
  have hpow_upper : (1 - x) ^ 6 ≤ 1 - 6 * x + 15 * x ^ 2 := by
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx0 3) hrest]
  have hd : 0 < 1 - x := by linarith only [hx]
  have hpow_lower : (1 : ℝ) / 2 ≤ (1 - x) ^ 6 := by
    calc
      _ ≤ ((12 : ℝ) / 13) ^ 6 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by linarith only [hx]) 6
  apply (le_div_iff₀ (pow_pos hd 6)).mpr
  have hscale := mul_le_mul_of_nonneg_left hpow_lower
    (show 0 ≤ 30 * x ^ 2 from mul_nonneg (by norm_num) (sq_nonneg x))
  nlinarith only [hpow_upper, hscale]

theorem residueFactor_ge_one_sub_inverse_square {θ : PlaneIndex} {p : ℕ} [Fact p.Prime]
    (hθ : LocallyAdmissible θ) (hp13 : 13 ≤ p) :
    1 - 30 / (p : ℝ) ^ 2 ≤ residueFactor θ p := by
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp13' : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp13
  have hratio : (1 : ℝ) / (p : ℝ) ≤ 1 / 13 := one_div_le_one_div_of_le (by norm_num) hp13'
  have hnat : p * p ≤ (goodLatticeResiduePairs θ p).card + 6 * p := by
    have hh := card_goodLatticeResiduePairs_ge (p := p) hθ
    omega
  have hcast : (p : ℝ) ^ 2 ≤ ((goodLatticeResiduePairs θ p).card : ℝ) + 6 * (p : ℝ) := by
    rw [pow_two]
    exact_mod_cast hnat
  have hdensity : 1 - 6 / (p : ℝ) ≤ ((goodLatticeResiduePairs θ p).card : ℝ) / (p : ℝ) ^ 2 := by
    apply (le_div_iff₀ (pow_pos hp0 2)).mpr
    calc
      _ = (p : ℝ) ^ 2 - 6 * (p : ℝ) := by field_simp [hp0.ne'] <;> ring
      _ ≤ _ := by linarith only [hcast]
  have hconv : 1 - 30 * (1 / (p : ℝ)) ^ 2 = 1 - 30 / (p : ℝ) ^ 2 := by
    field_simp [hp0.ne'] <;> ring
  have hconv' : 6 * (1 / (p : ℝ)) = 6 / (p : ℝ) := by simp [div_eq_mul_inv]
  have hnorm := normalized_six_ge (div_nonneg (by norm_num) hp0.le) hratio
  rw [hconv, hconv'] at hnorm
  exact hnorm.trans (by
    rw [residueFactor_eq_of_prime]
    exact div_le_div_of_nonneg_right hdensity (residueDenominator_bounds hp).1.le)

/-- The truncated normalized local product of every admissible plane is
uniformly bounded away from zero, independently of the plane and cutoff. -/
theorem uniform_residueFactor_product_lower_bound :
    ∃ d : ℝ, 0 < d ∧ ∀ (θ : PlaneIndex) (s : Finset ℕ), LocallyAdmissible θ →
      (∀ p ∈ s, p.Prime) → d ≤ ∏ p ∈ s, residueFactor θ p := by
  obtain ⟨d, hd, h⟩ := uniform_finite_factor_product_lower_bound 30 60
    (by norm_num) (by decide) (by norm_num)
    (fun _ => 1 / (60 : ℝ) ^ 2) (by intro p hp; norm_num)
  refine ⟨d, hd, ?_⟩
  intro θ s hθ hs
  apply h (residueFactor θ) s
  · intro p hps hp
    letI : Fact p.Prime := ⟨hs p hps⟩
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hs p hps).pos
    have hp60 : (p : ℝ) ≤ (60 : ℝ) := by exact_mod_cast hp
    exact (one_div_le_one_div_of_le (pow_pos hp0 2) (pow_le_pow_left₀ hp0.le hp60 2)).trans
      (residueFactor_ge_inverse_square hθ)
  · intro p hps hp
    letI : Fact p.Prime := ⟨hs p hps⟩
    exact residueFactor_ge_one_sub_inverse_square hθ (by omega)

end Jsp000881
