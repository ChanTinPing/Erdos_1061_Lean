module

public import Jsp000881.MaskedModel
import all Jsp000881.MaskedModel
public import Jsp000881.AffineTransfer
import all Jsp000881.AffineTransfer

public section

namespace Jsp000881

open scoped BigOperators

private theorem companion_indices (j : Fin 6) :
    ∃ a b : Fin 6, ∃ L : List (Fin 6), L.length = 3 ∧ a ≠ b ∧ j ∉ a :: b :: L ∧
      ∀ f : Fin 6 → ℂ, (∏ i ∈ Finset.univ.erase j, f i) = ((a :: b :: L).map f).prod := by
  classical
  let S := (Finset.univ : Finset (Fin 6)).erase j
  have hL : S.toList.length = 5 := by
    simp only [Finset.length_toList, S, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
  cases he : S.toList with
  | nil => simp [he] at hL
  | cons a rest =>
    cases hr : rest with
    | nil => simp [he, hr] at hL
    | cons b L =>
      have hs : S.toList = a :: b :: L := he.trans (congrArg (a :: ·) hr)
      have hlen : L.length = 3 := by rw [hs] at hL; simp only [List.length_cons] at hL; omega
      have hnd : (a :: b :: L).Nodup := hs ▸ S.nodup_toList
      refine ⟨a, b, L, hlen, ?_, ?_, ?_⟩
      · intro h
        exact (List.nodup_cons.mp hnd).1 (h.symm ▸ List.mem_cons_self)
      · intro h
        have hm : j ∈ S := Finset.mem_toList.mp (hs.symm ▸ h)
        exact (Finset.mem_erase.mp hm).1 rfl
      · intro f
        change (∏ i ∈ S, f i) = _
        rw [← hs, ← List.prod_toFinset f S.nodup_toList, Finset.toList_toFinset]

private noncomputable def mixedCyclicWeight (X p : ℕ) (j i : Fin 6) : ZMod p → ℂ :=
  cyclicWeight X p (if i.val < j.val then primeWeight else cramerWeight (primeUniformityCutoff X))

private theorem mixedCyclicWeight_intCast {X p : ℕ} (hp : X < p) (j i : Fin 6) {n : ℤ}
    (hn₁ : 1 ≤ n) (hn₂ : n ≤ (X : ℤ)) :
    mixedCyclicWeight X p j i (n : ZMod p) =
      ((if i.val < j.val then primeWeight n else cramerWeight (primeUniformityCutoff X) n) : ℝ) := by
  unfold mixedCyclicWeight
  rw [cyclicWeight_intCast hp _ hn₁ hn₂]
  split <;> simp_all

private theorem norm_mixedCyclicWeight_le {X p : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h₁ : ∀ n : ℤ, 1 ≤ n → n ≤ (X : ℤ) → |primeWeight n| ≤ B)
    (h₂ : ∀ n : ℤ, 1 ≤ n → n ≤ (X : ℤ) → |cramerWeight (primeUniformityCutoff X) n| ≤ B)
    (j i : Fin 6) (x : ZMod p) : ‖mixedCyclicWeight X p j i x‖ ≤ B := by
  unfold mixedCyclicWeight
  split
  · exact norm_cyclicWeight_le hB h₁ x
  · exact norm_cyclicWeight_le hB h₂ x

private noncomputable def fieldReplacementFactor (X p : ℕ) (θ : PlaneIndex) (j : Fin 6)
    (x : ZMod p × ZMod p) : ℂ :=
  primeCramerDifference X p ((integralRowMod θ p j).eval x.1 x.2) *
    ∏ i ∈ Finset.univ.erase j, mixedCyclicWeight X p j i ((integralRowMod θ p i).eval x.1 x.2)

private theorem masked_step_eq_cyclic {k p : ℕ} [Fact p.Prime] {θ : PlaneIndex}
    (hk : 40 ≤ k) (hθ : ParameterBox θ ((k : ℤ) ^ 7))
    (hp : 32 * primeRectangleRadius k < p) (j : Fin 6) :
    let T := (2 : ℤ) ^ k
    let X := primeRectangleRadius k
    let Q := primeUniformityCutoff X
    let mask := rectangleMask p T
    ((maskedRectangleMass mask Q θ T (j.val + 1) - maskedRectangleMass mask Q θ T j.val : ℝ) : ℂ) =
      ∑ x, fieldRectangleMask p T x * fieldReplacementFactor X p θ j x := by
  dsimp only
  let T := (2 : ℤ) ^ k
  let X := primeRectangleRadius k
  let Q := primeUniformityCutoff X
  let mask := rectangleMask p T
  change ((maskedRectangleMass mask Q θ T (j.val + 1) - maskedRectangleMass mask Q θ T j.val : ℝ) : ℂ) =
    ∑ x, fieldRectangleMask p T x * fieldReplacementFactor X p θ j x
  obtain ⟨_, ha, hb⟩ := large_dyadic_rectangle hk
  have hk₈ : 8 ≤ k := (by decide : (8 : ℕ) ≤ 40).trans hk
  have hXp : X < p := by change 32 * X < p at hp; omega
  have hXp' : 2 * (X : ℤ) < (p : ℤ) := by
    exact_mod_cast (show 2 * X < p by change 32 * X < p at hp; omega)
  have hR (nm : ℤ × ℤ) (hnm : nm ∈ latticeRectangle T) : |nm.1| ≤ (X : ℤ) ∧ |nm.2| ≤ (X : ℤ) :=
    let h := rectangle_point_radius hk₈ hθ hnm
    ⟨h.1, h.2.1⟩
  rw [fieldRectangle_sum (by positivity) ((by decide : (1 : ℤ) ≤ 8).trans ha)
    ((by decide : (1 : ℤ) ≤ 8).trans hb) hXp' hR,
    maskedRectangleMass_step, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro nm hnm
  have hval (i : Fin 6) :
      1 ≤ (sextupleOn θ nm).coord i ∧ (sextupleOn θ nm).coord i ≤ (X : ℤ) := by
    rw [← integralRow_eval]
    exact (rectangle_point_radius hk₈ hθ hnm).2.2 i
  have he (i : Fin 6) :
      (integralRowMod θ p i).eval (castRectanglePoint p nm).1 (castRectanglePoint p nm).2 =
        ((sextupleOn θ nm).coord i : ZMod p) :=
    integralRowMod_eval_cast θ p nm i
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, fieldReplacementFactor, he,
    primeCramerDifference_intCast hXp (hval j).1 (hval j).2, mask]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (mixedCyclicWeight_intCast hXp j i (hval i).1 (hval i).2).symm

/-- A single weighted prime replacement has the exact global Gowers bound
after embedding the integer rectangle into the prime field. -/
theorem masked_replacement_le {k p : ℕ} [Fact p.Prime] {θ : PlaneIndex}
    (hk : 40 ≤ k) (hθ : ParameterBox θ ((k : ℤ) ^ 7))
    (hp : 32 * primeRectangleRadius k < p)
    (hdet : determinantBound ((k : ℤ) ^ 7) < (p : ℤ))
    {B G : ℝ} (hB : 0 < B) (hG : 0 ≤ G)
    (h₁ : ∀ n : ℤ, 1 ≤ n → n ≤ (primeRectangleRadius k : ℤ) → |primeWeight n| ≤ B)
    (h₂ : ∀ n : ℤ, 1 ≤ n → n ≤ (primeRectangleRadius k : ℤ) →
      |cramerWeight (primeUniformityCutoff (primeRectangleRadius k)) n| ≤ B)
    (hU : gowersCubeMoment 5 (primeCramerDifference (primeRectangleRadius k) p) ≤ G ^ 32)
    (j : Fin 6) :
    let T := (2 : ℤ) ^ k
    let Q := primeUniformityCutoff (primeRectangleRadius k)
    let mask := rectangleMask p T
    |maskedRectangleMass mask Q θ T (j.val + 1) - maskedRectangleMass mask Q θ T j.val| ≤
      (p : ℝ) ^ 2 * B ^ 5 * G := by
  dsimp only
  let T := (2 : ℤ) ^ k
  let X := primeRectangleRadius k
  let Q := primeUniformityCutoff X
  let mask := rectangleMask p T
  let f := primeCramerDifference X p
  let g := mixedCyclicWeight X p j
  let C := fun x : ZMod p × ZMod p => fieldRectangleMask p T x * fieldReplacementFactor X p θ j x
  obtain ⟨a, b, L, hL, hab, hj, hprod⟩ := companion_indices j
  have hF (x : ZMod p × ZMod p) : fieldReplacementFactor X p θ j x =
      f ((integralRowMod θ p j).eval x.1 x.2) *
        ((a :: b :: L).map fun i => g i ((integralRowMod θ p i).eval x.1 x.2)).prod := by
    dsimp only [fieldReplacementFactor, f, g]
    rw [hprod]
  have hz : (100 : ℤ) ≤ (k : ℤ) ^ 7 :=
    (by decide : (100 : ℤ) ≤ (40 : ℤ) ^ 7).trans (pow_le_pow_left₀ (by decide) (by exact_mod_cast hk) 7)
  have hbound : ‖meanC C‖ ≤ B ^ 5 * G := by
    simp only [C, fieldRectangleMask, sideMask, hF]
    exact integralRows_triangle_gowers_bound hz hθ hdet j a b L hL hab hj f g hB
      (fun i x => norm_mixedCyclicWeight_le hB.le h₁ h₂ j i x) hG hU
      (triangleInterval_nonempty _ _) (triangleInterval_nonempty _ _) _ _
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsum : (∑ x, C x) = (p : ℂ) ^ 2 * meanC C := by
    unfold meanC
    simp only [Fintype.card_prod, ZMod.card, Nat.cast_mul, pow_two]
    field_simp [hpC] <;> ring
  change |maskedRectangleMass mask Q θ T (j.val + 1) - maskedRectangleMass mask Q θ T j.val| ≤ _
  calc
    _ = ‖((maskedRectangleMass mask Q θ T (j.val + 1) - maskedRectangleMass mask Q θ T j.val : ℝ) : ℂ)‖ :=
      by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∑ x, C x‖ := congrArg norm (masked_step_eq_cyclic hk hθ hp j)
    _ = (p : ℝ) ^ 2 * ‖meanC C‖ := by rw [hsum, norm_mul, norm_pow, Complex.norm_natCast]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hbound (by positivity)

end Jsp000881
