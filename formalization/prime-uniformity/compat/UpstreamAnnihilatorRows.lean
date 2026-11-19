import OAI.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
import OAI.Combinatorics.Progressions.Geometry.CommonNativeCoordinateCorrections

namespace PrimeUniformity

open Module OAI.Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

/-- A bounded quotient basis and a rational row presentation of the common
four-coordinate space of a horizontal layer. -/
theorem exists_bounded_common_coordinate_rows
    {s r N : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) (hd : 1 ≤ d.val) :
    ∃ m : ℕ, m ≤ W.dim ∧
      ∃ f : Basis (Fin m) ℚ (W.L ⧸ W.rank.filtration.layer d.val 2),
        (∀ i j, rationalLogHeight (f.repr ((W.rank.filtration.layer d.val 2).mkQ (W.model.basis j)) i) ≤
          (P + 3) ^ 7) ∧
        ∃ n : ℕ, n ≤ 4 * m ∧
          ∃ ℓ : (Fin 4 → Fin m → ℚ) →ₗ[ℚ] (Fin n → ℚ),
            Function.Surjective ℓ ∧ LinearMap.ker ℓ = D.coordinateSpace d f ∧
            ∀ k i j, rationalLogHeight
              (ℓ (LinearMap.single ℚ (fun _ : Fin 4 => Fin m → ℚ) k ((Pi.basisFun ℚ (Fin m)) i)) j) ≤
                (4 * P + horizontalCoordinateBudget P + 3) ^ 7 := by
  obtain ⟨m, hm, f, hf, v, hv, hvH⟩ := D.exists_bounded_coordinate_generators hP hbP d hd
  let A := 4 * P + horizontalCoordinateBudget P
  have hB := horizontalCoordinateBudget_nonneg hP
  have hA : 0 ≤ A := add_nonneg (mul_nonneg (by norm_num) hP) hB
  have hBA : horizontalCoordinateBudget P ≤ A :=
    le_add_of_nonneg_left (mul_nonneg (by norm_num) hP)
  have hdim : (W.dim : ℝ) ≤ P := W.complexity.1.1.trans hbP
  have hcount : (Fintype.card (Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim))) : ℝ) ≤ A := by
    simp only [Fintype.card_fin, Fintype.card_sigma, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    exact (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)).trans
      (le_add_of_nonneg_right hB)
  obtain ⟨n, hn, ℓ, hsurj, hker, hheight⟩ :=
    exists_bounded_four_annihilator (Pi.basisFun ℚ (Fin m)) _ v hv hA hcount
      (fun a k i => by simpa only [Pi.basisFun_repr] using (hvH a k i).trans hBA)
  exact ⟨m, hm, f, hf, n, by simpa only [Fintype.card_fin] using hn, ℓ, hsurj, hker, hheight⟩

end PrimeUniformity

#print axioms PrimeUniformity.exists_bounded_common_coordinate_rows
