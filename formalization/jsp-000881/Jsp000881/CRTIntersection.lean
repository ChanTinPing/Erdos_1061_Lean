module

public import Jsp000881.ResidueRectangles
import all Jsp000881.ResidueRectangles
public import Jsp000881.Products
import all Jsp000881.Products
public import Mathlib.Data.Nat.GCD.BigOperators

public section

namespace Jsp000881

open scoped BigOperators

/-- The number of residue pairs modulo the product of distinct primes
realizing prescribed local conditions is the product of the local counts. -/
theorem crt_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : (p : ℕ) → Finset (ZMod p × ZMod p)) :
    ∃ R : Finset (ZMod (∏ p ∈ P, p) × ZMod (∏ p ∈ P, p)),
      R.card = ∏ p ∈ P, (A p).card ∧
      ∀ a b : ℤ, ((a : ZMod (∏ p ∈ P, p)), (b : ZMod (∏ p ∈ P, p))) ∈ R ↔
        ∀ p ∈ P, ((a : ZMod p), (b : ZMod p)) ∈ A p := by
  classical
  suffices hmain : ∀ D : ℕ, D = (∏ p ∈ P, p) →
      ∃ R : Finset (ZMod D × ZMod D),
        R.card = ∏ p ∈ P, (A p).card ∧
        ∀ a b : ℤ, ((a : ZMod D), (b : ZMod D)) ∈ R ↔
          ∀ p ∈ P, ((a : ZMod p), (b : ZMod p)) ∈ A p by
    exact hmain _ rfl
  induction P using Finset.induction_on with
  | empty =>
    intro D hD
    have hOne : D = 1 := hD.trans (Finset.prod_empty)
    clear hD
    subst D
    simp only [Finset.prod_empty]
    refine ⟨{(0, 0)}, Finset.card_singleton _, ?_⟩
    intro a b
    have hpair : ((a : ZMod 1), (b : ZMod 1)) = (0, 0) :=
      Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    rw [hpair] <;> simp
  | @insert p P hp ih =>
    intro D hD
    have hMul : D = p * (∏ q ∈ P, q) := hD.trans (Finset.prod_insert hp)
    clear hD
    subst D
    have hp' : p.Prime := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ P, q) := Nat.coprime_prod_right_iff.mpr fun q hq =>
      (Nat.coprime_primes hp' (hP' q hq)).mpr (fun he => hp (he.symm ▸ hq))
    obtain ⟨R, hcard, hR⟩ := ih hP' _ rfl
    simp only [Finset.prod_insert hp]
    refine ⟨liftResiduePairs hcop (A p) R, by rw [card_liftResiduePairs, hcard], ?_⟩
    intro a b
    rw [mem_liftResiduePairs, hR]
    simp only [Finset.forall_mem_insert]

private noncomputable def badLatticeResidues (θ : PlaneIndex) (p : ℕ) :
    Finset (ZMod p × ZMod p) := by
  classical
  cases p with
  | zero => exact ∅
  | succ p =>
    exact (Finset.univ : Finset (ZMod (p + 1) × ZMod (p + 1))).filter fun nm =>
      ∃ i : Fin 6, (integralRowMod θ (p + 1) i).eval nm.1 nm.2 = 0

private theorem mem_badLatticeResidues (θ : PlaneIndex) {p : ℕ} (hp : p.Prime) (a b : ℤ) :
    ((a : ZMod p), (b : ZMod p)) ∈ badLatticeResidues θ p ↔
      ∃ i : Fin 6, (p : ℤ) ∣ (sextupleOn θ (a, b)).coord i := by
  classical
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ p =>
    simp only [badLatticeResidues, Finset.mem_filter, Finset.mem_univ, true_and]
    apply exists_congr
    intro i
    rw [show (integralRowMod θ (p + 1) i).eval (a : ZMod (p + 1)) (b : ZMod (p + 1)) =
        ((sextupleOn θ (a, b)).coord i : ZMod (p + 1)) from integralRowMod_eval_cast θ _ (a, b) i]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

noncomputable def localBadDensity (θ : PlaneIndex) (p : ℕ) : ℝ :=
  ((badLatticeResidues θ p).card : ℝ) / (p : ℝ) ^ 2

theorem localBadDensity_eq_one_sub_good (θ : PlaneIndex) {p : ℕ} [Fact p.Prime] :
    localBadDensity θ p = 1 - ((goodLatticeResiduePairs θ p).card : ℝ) / (p : ℝ) ^ 2 := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hbad : badLatticeResidues θ p =
      Finset.univ.filter fun nm : ZMod p × ZMod p =>
        ¬ (∀ i, (integralRowMod θ p i).eval nm.1 nm.2 ≠ 0) := by
    cases p with
    | zero => exact (Nat.not_prime_zero hp).elim
    | succ p =>
      ext nm
      simp only [badLatticeResidues, Finset.mem_filter, Finset.mem_univ, true_and]
      push_neg <;> rfl
  have hcard : (goodLatticeResiduePairs θ p).card + (badLatticeResidues θ p).card = p * p := by
    rw [hbad, goodLatticeResiduePairs]
    simpa only [Finset.card_univ, Fintype.card_prod, ZMod.card] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p × ZMod p)))
        (fun nm => ∀ i, (integralRowMod θ p i).eval nm.1 nm.2 ≠ 0)
  have hc : ((goodLatticeResiduePairs θ p).card : ℝ) + ((badLatticeResidues θ p).card : ℝ) =
      (p : ℝ) ^ 2 := by rw [pow_two]; exact_mod_cast hcard
  unfold localBadDensity
  field_simp [hp0.ne'] <;> linarith only [hc]

theorem localBadDensity_bounds (θ : PlaneIndex) {p : ℕ} (hp : p.Prime) :
    0 ≤ localBadDensity θ p ∧ localBadDensity θ p ≤ 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · unfold localBadDensity
    positivity
  · rw [localBadDensity_eq_one_sub_good]
    exact sub_le_self _ (by positivity)

theorem localBadDensity_le_six_div {θ : PlaneIndex} (hθ : LocallyAdmissible θ)
    {p : ℕ} (hp : p.Prime) : localBadDensity θ p ≤ 6 / (p : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hNat := Nat.sub_le_iff_le_add.mp (card_goodLatticeResiduePairs_ge (p := p) hθ)
  have hcount : (p : ℝ) ^ 2 ≤ ((goodLatticeResiduePairs θ p).card : ℝ) + 6 * (p : ℝ) := by
    rw [pow_two]
    exact_mod_cast hNat
  rw [localBadDensity_eq_one_sub_good, sub_le_iff_le_add]
  calc
    1 ≤ (((goodLatticeResiduePairs θ p).card : ℝ) + 6 * (p : ℝ)) / (p : ℝ) ^ 2 :=
      (le_div_iff₀ (pow_pos hp0 2)).mpr (by simpa using hcount)
    _ = _ := by field_simp [hp0.ne'] <;> ring

noncomputable def badIntersection (θ : PlaneIndex) (P : Finset ℕ)
    (start₁ len₁ start₂ len₂ : ℤ) : Finset (ℤ × ℤ) := by
  classical
  exact ((interval start₁ len₁).product (interval start₂ len₂)).filter fun nm =>
    ∀ p ∈ P, ∃ i : Fin 6, (p : ℤ) ∣ (sextupleOn θ nm).coord i

/-- Finite CRT main term with the rectangle discrepancy required in the
truncated Cramér sieve. The result applies to each squarefree modulus. -/
theorem badIntersection_discrepancy (θ : PlaneIndex) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (start₁ len₁ start₂ len₂ : ℤ) (h₁ : 0 ≤ len₁) (h₂ : 0 ≤ len₂) :
    let D := (∏ p ∈ P, p)
    |((badIntersection θ P start₁ len₁ start₂ len₂).card : ℝ) -
      (len₁ : ℝ) * (len₂ : ℝ) * (∏ p ∈ P, localBadDensity θ p)| ≤
      ((len₁ : ℝ) + (len₂ : ℝ)) * (D : ℝ) + (D : ℝ) ^ 2 := by
  classical
  let D : ℕ := ∏ p ∈ P, p
  change _ ≤ ((len₁ : ℝ) + (len₂ : ℝ)) * (D : ℝ) + (D : ℝ) ^ 2
  have hD : 0 < D := Finset.prod_pos fun p hp => (hP p hp).pos
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  letI : NeZero D := ⟨hD.ne'⟩
  obtain ⟨R, hRcard, hR⟩ := crt_prime_product P hP (badLatticeResidues θ)
  have he : badIntersection θ P start₁ len₁ start₂ len₂ =
      rectangleWithResidues start₁ len₁ start₂ len₂ R := by
    ext nm
    simp only [badIntersection, rectangleWithResidues, Finset.mem_filter]
    rw [hR]
    apply and_congr_right
    intro _
    constructor
    · intro h p hp
      exact (mem_badLatticeResidues θ (hP p hp) _ _).mpr (h p hp)
    · intro h p hp
      exact (mem_badLatticeResidues θ (hP p hp) _ _).mp (h p hp)
  have hprod : (∏ p ∈ P, localBadDensity θ p) = (R.card : ℝ) / (D : ℝ) ^ 2 := by
    simp only [localBadDensity, Finset.prod_div_distrib, hRcard, Nat.cast_prod, D, Finset.prod_pow]
  have hcard : (R.card : ℝ) ≤ (D : ℝ) ^ 2 := by
    have hcard' : R.card ≤ D * D := by
      simpa only [Fintype.card_prod, ZMod.card] using Finset.card_le_univ R
    rw [pow_two]
    exact_mod_cast hcard'
  rw [he, hprod]
  have hmain : (len₁ : ℝ) * (len₂ : ℝ) * (R.card / (D : ℝ) ^ 2) =
      (R.card : ℝ) * ((len₁ : ℝ) / (D : ℝ) * ((len₂ : ℝ) / (D : ℝ))) := by
    field_simp [hDr.ne'] <;> ring
  rw [hmain]
  have h₁' : (0 : ℝ) ≤ len₁ := by exact_mod_cast h₁
  have h₂' : (0 : ℝ) ≤ len₂ := by exact_mod_cast h₂
  calc
    _ ≤ (R.card : ℝ) * ((len₁ : ℝ) / (D : ℝ) + (len₂ : ℝ) / (D : ℝ) + 1) :=
      rectangleWithResidues_discrepancy hD start₁ len₁ start₂ len₂ h₁ h₂ R
    _ ≤ (D : ℝ) ^ 2 * ((len₁ : ℝ) / (D : ℝ) + (len₂ : ℝ) / (D : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp [hDr.ne'] <;> ring

end Jsp000881
