module

public import PrimeUniformity.ResidueIntervals
public import Jsp000881.SieveBounds
public import Mathlib.Data.Int.CardIntervalMod

@[expose] public section

namespace Jsp000881

open scoped BigOperators

export PrimeUniformity (residueSlice_discrepancy)

/-- Lattice-point error for a single pair of residue classes in a rectangle. -/
theorem pair_residue_discrepancy (start₁ len₁ start₂ len₂ : ℤ) {p : ℕ} (hp : 0 < p)
    (h₁ : 0 ≤ len₁) (h₂ : 0 ≤ len₂) (r : ZMod p × ZMod p) :
    |(((residueSlice start₁ len₁ r.1).product (residueSlice start₂ len₂ r.2)).card : ℝ) -
      (len₁ : ℝ) / (p : ℝ) * ((len₂ : ℝ) / (p : ℝ))| ≤
        (len₁ : ℝ) / (p : ℝ) + (len₂ : ℝ) / (p : ℝ) + 1 := by
  let a : ℝ := (len₁ : ℝ) / (p : ℝ)
  let b : ℝ := (len₂ : ℝ) / (p : ℝ)
  let x : ℝ := (residueSlice start₁ len₁ r.1).card
  let y : ℝ := (residueSlice start₂ len₂ r.2).card
  have ha : 0 ≤ a := div_nonneg (by exact_mod_cast h₁) (by exact_mod_cast hp.le)
  have hb : 0 ≤ b := div_nonneg (by exact_mod_cast h₂) (by exact_mod_cast hp.le)
  have hx : |x - a| ≤ 1 := residueSlice_discrepancy start₁ len₁ hp h₁ r.1
  have hy : |y - b| ≤ 1 := residueSlice_discrepancy start₂ len₂ hp h₂ r.2
  simp only [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
  change |x * y - a * b| ≤ a + b + 1
  rw [show x * y - a * b = (a * (y - b) + b * (x - a)) + (x - a) * (y - b) by ring]
  calc
    _ ≤ |a * (y - b) + b * (x - a)| + |(x - a) * (y - b)| := abs_add_le _ _
    _ ≤ (|a * (y - b)| + |b * (x - a)|) + |(x - a) * (y - b)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by
      simp only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      have h₁' := mul_le_mul_of_nonneg_left hy ha
      have h₂' := mul_le_mul_of_nonneg_left hx hb
      have h₃' := mul_le_mul hx hy (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      linarith only [h₁', h₂', h₃']

/-- Points inside the integer rectangle whose pair of residues belongs to
the selected set. -/
noncomputable def rectangleWithResidues {p : ℕ} (start₁ len₁ start₂ len₂ : ℤ)
    (R : Finset (ZMod p × ZMod p)) : Finset (ℤ × ℤ) :=
  ((interval start₁ len₁).product (interval start₂ len₂)).filter
    fun nm => ((nm.1 : ZMod p), (nm.2 : ZMod p)) ∈ R

private theorem card_rectangleWithResidues {p : ℕ} (start₁ len₁ start₂ len₂ : ℤ)
    (R : Finset (ZMod p × ZMod p)) :
    (rectangleWithResidues start₁ len₁ start₂ len₂ R).card =
      ∑ r ∈ R, ((residueSlice start₁ len₁ r.1).product (residueSlice start₂ len₂ r.2)).card := by
  classical
  let f := fun nm : ℤ × ℤ => ((nm.1 : ZMod p), (nm.2 : ZMod p))
  have hf : ∀ nm ∈ rectangleWithResidues start₁ len₁ start₂ len₂ R, f nm ∈ R := by
    intro nm hnm
    unfold rectangleWithResidues at hnm
    exact (Finset.mem_filter.mp hnm).2
  rw [Finset.card_eq_sum_card_fiberwise hf]
  apply Finset.sum_congr rfl
  intro r hr
  obtain ⟨r₁, r₂⟩ := r
  congr 1
  ext x
  simp only [rectangleWithResidues, residueSlice, Finset.product_eq_sprod,
    Finset.mem_filter, Finset.mem_product,
    f, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hx₁, hx₂⟩, _⟩, h₁, h₂⟩
    exact ⟨⟨hx₁, h₁⟩, hx₂, h₂⟩
  · rintro ⟨⟨hx₁, h₁⟩, hx₂, h₂⟩
    exact ⟨⟨⟨hx₁, hx₂⟩, by rwa [h₁, h₂]⟩, h₁, h₂⟩

theorem rectangleWithResidues_discrepancy {p : ℕ} (hp : 0 < p)
    (start₁ len₁ start₂ len₂ : ℤ) (h₁ : 0 ≤ len₁) (h₂ : 0 ≤ len₂)
    (R : Finset (ZMod p × ZMod p)) :
    |((rectangleWithResidues start₁ len₁ start₂ len₂ R).card : ℝ) -
      (R.card : ℝ) * ((len₁ : ℝ) / (p : ℝ) * ((len₂ : ℝ) / (p : ℝ)))| ≤
      (R.card : ℝ) * ((len₁ : ℝ) / (p : ℝ) + (len₂ : ℝ) / (p : ℝ) + 1) := by
  let main := (len₁ : ℝ) / (p : ℝ) * ((len₂ : ℝ) / (p : ℝ))
  let err := (len₁ : ℝ) / (p : ℝ) + (len₂ : ℝ) / (p : ℝ) + 1
  let card := fun r : ZMod p × ZMod p =>
    (((residueSlice start₁ len₁ r.1).product (residueSlice start₂ len₂ r.2)).card : ℝ)
  have hC : ((rectangleWithResidues start₁ len₁ start₂ len₂ R).card : ℝ) = ∑ r ∈ R, card r :=
    by
      dsimp only [card]
      rw [← Nat.cast_sum]
      exact_mod_cast (card_rectangleWithResidues start₁ len₁ start₂ len₂ R)
  have hmain : (R.card : ℝ) * main = ∑ _r ∈ R, main := by rw [Finset.sum_const, nsmul_eq_mul]
  change |((rectangleWithResidues start₁ len₁ start₂ len₂ R).card : ℝ) -
    (R.card : ℝ) * main| ≤ (R.card : ℝ) * err
  rw [hC, hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ R, |card r - main| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ R, err := Finset.sum_le_sum fun r _ =>
      pair_residue_discrepancy start₁ len₁ start₂ len₂ hp h₁ h₂ r
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The CRT for two coordinates sends independent residue conditions to a product. -/
def residuePairCRT {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n) × ZMod (m * n)) ≃ ((ZMod m × ZMod m) × (ZMod n × ZMod n)) :=
  ((ZMod.chineseRemainder h).toEquiv.prodCongr (ZMod.chineseRemainder h).toEquiv).trans
    (Equiv.prodProdProdComm _ _ _ _)

theorem residuePairCRT_intCast {m n : ℕ} (h : m.Coprime n) (a b : ℤ) :
    residuePairCRT h ((a : ZMod (m * n)), (b : ZMod (m * n))) =
      (((a : ZMod m), (b : ZMod m)), ((a : ZMod n), (b : ZMod n))) := by
  simp only [residuePairCRT, Equiv.trans_apply, Equiv.prodCongr_apply]
  change (Equiv.prodProdProdComm _ _ _ _)
    ((ZMod.chineseRemainder h) (a : ZMod (m * n)),
      (ZMod.chineseRemainder h) (b : ZMod (m * n))) = _
  rw [map_intCast, map_intCast]
  rfl

def liftResiduePairs {m n : ℕ} (h : m.Coprime n)
    (A : Finset (ZMod m × ZMod m)) (B : Finset (ZMod n × ZMod n)) :
    Finset (ZMod (m * n) × ZMod (m * n)) :=
  (A.product B).map (residuePairCRT h).symm.toEmbedding

theorem card_liftResiduePairs {m n : ℕ} (h : m.Coprime n)
    (A : Finset (ZMod m × ZMod m)) (B : Finset (ZMod n × ZMod n)) :
    (liftResiduePairs h A B).card = A.card * B.card := by
  rw [liftResiduePairs, Finset.card_map, Finset.product_eq_sprod, Finset.card_product]

theorem mem_liftResiduePairs {m n : ℕ} (h : m.Coprime n)
    (A : Finset (ZMod m × ZMod m)) (B : Finset (ZMod n × ZMod n)) (a b : ℤ) :
    ((a : ZMod (m * n)), (b : ZMod (m * n))) ∈ liftResiduePairs h A B ↔
    ((a : ZMod m), (b : ZMod m)) ∈ A ∧ ((a : ZMod n), (b : ZMod n)) ∈ B := by
  rw [liftResiduePairs, Finset.product_eq_sprod, Finset.mem_map]
  constructor
  · rintro ⟨v, hv, he⟩
    have hres := congrArg (residuePairCRT h) he
    change residuePairCRT h ((residuePairCRT h).symm v) =
      residuePairCRT h ((a : ZMod (m * n)), (b : ZMod (m * n))) at hres
    rw [Equiv.apply_symm_apply, residuePairCRT_intCast] at hres
    subst v
    exact Finset.mem_product.mp hv
  · intro hAB
    refine ⟨(((a : ZMod m), (b : ZMod m)), ((a : ZMod n), (b : ZMod n))),
      Finset.mem_product.mpr hAB, ?_⟩
    change (residuePairCRT h).symm _ = _
    rw [← residuePairCRT_intCast h a b, Equiv.symm_apply_apply]

end Jsp000881
