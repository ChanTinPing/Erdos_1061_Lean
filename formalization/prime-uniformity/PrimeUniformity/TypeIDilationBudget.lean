module

public import PrimeUniformity.TypeIIDilationBudget
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped Classical BigOperators

/-- Fixed-degree Type I recovery needs only an exponential cofactor scale.
Use the two-variable estimate with the second coordinate zero when the
dyadic band is long, and clear a single sampled dilation when it is short. -/
theorem exists_uniform_typeI_coefficient_recovery (s : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧
      ∀ {J : Fin s → Type*} [∀ j, Fintype (J j)] (θ : ∀ j, J j → ℝ)
        (m : ∀ j, J j → ℕ) (_hm : ∀ j i, 0 < m j i) (L : ℕ) {t H X₀ X : ℝ},
      1 ≤ t → 0 ≤ H → H ≤ Real.exp t → (∀ j i, (m j i : ℝ) ≤ Real.exp t) →
      (Fintype.card ((Σ j : Fin s, J j) × Bool) : ℝ) ≤ t →
      0 < L → Real.exp ((C : ℝ) * t) ≤ X₀ / L → 0 < X → X * Real.exp (-t) ≤ X₀ →
      ∀ (S : Finset ℕ), S ⊆ dyadicDilationInterval L →
      Real.exp (-t) * ((dyadicDilationInterval L).card : ℝ) ≤ S.card →
      (∀ d ∈ S, ∀ j i, ∃ a : ℤ,
        |((m j i : ℝ) * θ j i) * (d : ℝ) ^ (j.val + 1) - a| ≤ H / (X₀ / L) ^ (j.val + 1)) →
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((C : ℝ) * t ^ 2) ∧
        ∀ j i, ∃ a : ℤ, |(q : ℝ) * θ j i - a| ≤ Real.exp ((C : ℝ) * t ^ 2) / X ^ (j.val + 1) := by
  obtain ⟨C₀, hC₀, hTypeII⟩ := exists_uniform_typeII_coefficient_recovery s
  let K := (C₀ + 1) * (s + 1)
  let C := 2 * K
  have hC₀K : C₀ ≤ K := (Nat.le_succ C₀).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos s))
  have hKC : K ≤ C := Nat.le_mul_of_pos_left _ (by decide)
  have hC₀C : C₀ ≤ C := hC₀K.trans hKC
  refine ⟨C, hC₀.trans hC₀C, ?_⟩
  intro J _ θ m hm L t H X₀ X ht hH hHt hmt hcard hL hside hX hX₀ S hS hdense hnear
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have hC₀CR : (C₀ : ℝ) ≤ C := Nat.cast_le.mpr hC₀C
  let T := dyadicDilationInterval L
  by_cases hlong : Real.exp ((C₀ : ℝ) * t) ≤ (L : ℝ)
  · let θ₂ (j : Fin s) (i : J j) (b : Bool) := if b then θ j i else 0
    have hSide₀ : Real.exp ((C₀ : ℝ) * t) ≤ X₀ / L :=
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC₀CR ht₀)).trans hside
    have hS₂ : S ×ˢ T ⊆ T ×ˢ T := Finset.product_subset_product hS (by rfl)
    have hdense₂ : Real.exp (-t) * (T.card : ℝ) ^ 2 ≤ ((S ×ˢ T).card : ℝ) := by
      rw [Finset.card_product, Nat.cast_mul, pow_two, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hdense (Nat.cast_nonneg _)
    have hnear₂ (d : ℕ × ℕ) (hd : d ∈ S ×ˢ T) (j : Fin s) (i : J j) : ∃ a : ℤ,
        |((m j i : ℝ) * θ₂ j i true) * (d.1 : ℝ) ^ (j.val + 1) +
          ((m j i : ℝ) * θ₂ j i false) * (d.2 : ℝ) ^ (j.val + 1) - a| ≤
            H / (X₀ / L) ^ (j.val + 1) := by
      simpa [θ₂] using hnear d.1 (Finset.mem_product.mp hd).1 j i
    obtain ⟨q, hq, hqC, ha⟩ := hTypeII θ₂ m hm L ht hH hHt hmt hcard hlong hSide₀ hX hX₀
      (S ×ˢ T) hS₂ hdense₂ hnear₂
    have hExp : Real.exp ((C₀ : ℝ) * t ^ 2) ≤ Real.exp ((C : ℝ) * t ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC₀CR (sq_nonneg t))
    refine ⟨q, hq, hqC.trans hExp, fun j i => ?_⟩
    obtain ⟨a, ha'⟩ := ha j i true
    exact ⟨a, (by simpa [θ₂] using ha' : |(q : ℝ) * θ j i - (a : ℝ)| ≤ _).trans
      (div_le_div_of_nonneg_right hExp (pow_nonneg hX.le _))⟩
  · have hshort : (L : ℝ) ≤ Real.exp ((C₀ : ℝ) * t) := (lt_of_not_ge hlong).le
    have hT : T.Nonempty := ⟨L, Finset.mem_Ico.mpr (by omega)⟩
    have hTpos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hT)
    have hSpos : 0 < (S.card : ℝ) := (mul_pos (Real.exp_pos _) hTpos).trans_le hdense
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hSpos)
    have hdBounds := Finset.mem_Ico.mp (hS hd)
    have hdpos : 0 < d := by omega
    have hdL : d ≤ L := by omega
    let U := Real.exp (((C₀ : ℝ) + 1) * t)
    have hU₁ : 1 ≤ U := Real.one_le_exp (by positivity)
    have hU₀ : 0 ≤ U := zero_le_one.trans hU₁
    have htU : Real.exp t ≤ U := Real.exp_le_exp.mpr (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (Nat.cast_nonneg C₀) : (1 : ℝ) ≤ C₀ + 1) ht₀)
    have hLU : Real.exp ((C₀ : ℝ) * t) ≤ U := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) ht₀)
    have hdU : (d : ℝ) ≤ U := (Nat.cast_le.mpr hdL).trans (hshort.trans hLU)
    have hHU : H ≤ U := hHt.trans htU
    have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
    have hX₀pos : 0 < X₀ := (mul_pos hX (Real.exp_pos _)).trans_le hX₀
    have hScale : X ≤ U * (X₀ / L) := by
      calc
        X = Real.exp t * (X * Real.exp (-t)) := by rw [Real.exp_neg]; field_simp
        _ ≤ Real.exp t * X₀ := mul_le_mul_of_nonneg_left hX₀ (Real.exp_pos _).le
        _ = (Real.exp t * L) * (X₀ / L) := by field_simp [hLpos.ne']
        _ ≤ (Real.exp t * Real.exp ((C₀ : ℝ) * t)) * (X₀ / L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hshort (Real.exp_pos _).le)
            (div_nonneg hX₀pos.le hLpos.le)
        _ = U * (X₀ / L) := by
          rw [← Real.exp_add]
          congr 2
          ring
    let I := Σ j : Fin s, J j
    let B := ⌊U ^ (s + 1)⌋₊
    have hRow (u : I) : ∃ q : ℕ, ∃ a : ℤ,
        0 < q ∧ q ≤ B ∧ |(q : ℝ) * θ u.1 u.2 - a| ≤ U ^ (s + 1) / X ^ (u.1.val + 1) := by
      obtain ⟨j, i⟩ := u
      let k := j.val + 1
      have hk : k ≤ s := j.isLt
      have hdPow : (d : ℝ) ^ k ≤ U ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hdU _
      have hqU : ((m j i * d ^ k : ℕ) : ℝ) ≤ U ^ (s + 1) := by
        rw [Nat.cast_mul, Nat.cast_pow]
        calc
          _ ≤ U * U ^ k := mul_le_mul ((hmt j i).trans htU) hdPow (by positivity) hU₀
          _ = U ^ (k + 1) := by rw [show U ^ (k + 1) = U ^ k * U from pow_succ U k, mul_comm]
          _ ≤ _ := pow_le_pow_right₀ hU₁ (Nat.succ_le_succ hk)
      obtain ⟨a, ha⟩ := hnear d hd j i
      refine ⟨m j i * d ^ k, a, Nat.mul_pos (hm j i) (pow_pos hdpos _), Nat.le_floor hqU, ?_⟩
      have hErr : H / (X₀ / L) ^ k ≤ U ^ (s + 1) / X ^ k := by
        apply (div_le_div_iff₀ (pow_pos (div_pos hX₀pos hLpos) k) (pow_pos hX k)).mpr
        have hPow : X ^ k ≤ U ^ k * (X₀ / L) ^ k :=
          (pow_le_pow_left₀ hX.le hScale k).trans_eq (mul_pow _ _ _)
        calc
          _ ≤ U * (U ^ k * (X₀ / L) ^ k) := mul_le_mul hHU hPow (pow_nonneg hX.le _) hU₀
          _ = U ^ (k + 1) * (X₀ / L) ^ k := by rw [pow_succ]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hU₁ (Nat.succ_le_succ hk)) (by positivity)
      have ha' : |((m j i * d ^ k : ℕ) : ℝ) * θ j i - (a : ℝ)| ≤ H / (X₀ / L) ^ k := by
        rw [Nat.cast_mul, Nat.cast_pow, mul_right_comm]
        exact ha
      exact ha'.trans hErr
    obtain ⟨q, hq, hqB, ha⟩ := common_denominator_of_bounded_coefficient_estimates
      (fun u : I => θ u.1 u.2) (fun u => U ^ (s + 1) / X ^ (u.1.val + 1)) (fun _ => B) hRow
    have hIcard : (Fintype.card I : ℝ) ≤ t := by
      have hh := hcard
      rw [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat] at hh
      have hnon : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
      exact (by nlinarith only [hnon] : (Fintype.card I : ℝ) ≤ (Fintype.card I : ℝ) * 2).trans hh
    have hPower (k : ℕ) : (U ^ (s + 1)) ^ k = Real.exp ((K : ℝ) * t * (k : ℝ)) := by
      dsimp only [U, K]
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      push_cast
      congr 1
      ring
    have hProd : (↑(∏ _ : I, B) : ℝ) ≤ Real.exp ((K : ℝ) * t ^ 2) := by
      rw [Finset.prod_const, Finset.card_univ, Nat.cast_pow]
      calc
        _ ≤ (U ^ (s + 1)) ^ Fintype.card I :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (pow_nonneg hU₀ _)) _
        _ = Real.exp ((K : ℝ) * t * (Fintype.card I : ℝ)) := hPower _
        _ ≤ _ := Real.exp_le_exp.mpr (by
          rw [pow_two, ← mul_assoc]
          exact mul_le_mul_of_nonneg_left hIcard (mul_nonneg (Nat.cast_nonneg K) ht₀))
    have hUn : U ^ (s + 1) ≤ Real.exp ((K : ℝ) * t ^ 2) := by
      have htt : t ≤ t ^ 2 := by nlinarith only [mul_nonneg ht₀ (sub_nonneg.mpr ht)]
      calc
        _ = Real.exp ((K : ℝ) * t) := by
          simpa only [pow_one, Nat.cast_one, mul_one] using hPower 1
        _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htt (Nat.cast_nonneg _))
    have hExp : Real.exp ((K : ℝ) * t ^ 2) ≤ Real.exp ((C : ℝ) * t ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hKC) (sq_nonneg t))
    refine ⟨q, hq, ((Nat.cast_le.mpr hqB).trans hProd).trans hExp, fun j i => ?_⟩
    obtain ⟨a, ha'⟩ := ha ⟨j, i⟩
    refine ⟨a, ha'.trans ?_⟩
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hX.le _)
    calc
      _ ≤ Real.exp ((K : ℝ) * t ^ 2) * Real.exp ((K : ℝ) * t ^ 2) :=
        mul_le_mul hProd hUn (pow_nonneg hU₀ _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; dsimp only [C]; push_cast; congr 1; ring

end PrimeUniformity
