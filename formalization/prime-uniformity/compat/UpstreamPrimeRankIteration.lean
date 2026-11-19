import UpstreamNativePrimeTests
import OAI.Combinatorics.Progressions.Polynomial.RaisedDegreeRank
import OAI.Combinatorics.Progressions.Nilpotent.NativeRankZeroNiltest
import OAI.Combinatorics.Progressions.Nilpotent.RankInvariantNiltestBudget

namespace PrimeUniformity

open Filter Module OAI.Erdos3
open scoped BigOperators TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- A progression-supported native test with a controlled rank structure. -/
structure NativeRankedPrimeTest (s r X : ℕ) (p : ℝ) where
  test : NativePrimeTest s X p
  rank : test.model.DegreeRankStructure r
  complexity : rank.ComplexityLE p

/-- Attach the canonical initial rank while preserving the test evaluations. -/
theorem nativePrimeTest_init_rank (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : ℕ} {p : ℝ} (W : NativePrimeTest s X p), 0 ≤ p →
      ∃ V : NativeRankedPrimeTest s s X ((p + C) ^ C), V.test.eval = W.eval := by
  obtain ⟨C, hC, hinit⟩ := RationalFilteredNilmanifold.exists_native_degree_rank_structure s
  refine ⟨C, hC, ?_⟩
  intro X p W hp
  have hb : p ≤ (p + C) ^ C := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    have hbase : 1 ≤ p + (C : ℝ) := by linarith
    exact (by linarith : p ≤ p + C).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ C by omega))
  obtain ⟨R, _, hR⟩ := hinit W.model hp W.complexity.1
  exact ⟨⟨{ W with complexity := W.complexity.mono hb }, R, hR⟩, rfl⟩

/-- Rank zero makes the top degree layer trivial. Drop it with no loss in
complexity, progression support, or evaluational equality. -/
theorem nativeRankedPrimeTest_zero_drop {s X : ℕ} {p : ℝ}
    (W : NativeRankedPrimeTest (s + 1) 0 X p) :
    ∃ G : NativePrimeTest s X p, G.eval = W.test.eval := by
  have htop : W.test.model.filtration.layer (s + 1) = ⊥ := by
    rw [← W.rank.associated]
    change W.rank.filtration.layer (s + 1) 0 = ⊥
    rw [W.rank.filtration.rank_zero_eq_one]
    exact W.rank.filtration.terminal
  let G : NativePrimeTest s X p :=
    { L := W.test.L, dim := W.test.dim, model := W.test.model.dropTop htop
      test := W.test.test.dropTop htop, complexity := W.test.test.dropTop_complexity htop W.test.complexity
      bound := W.test.bound
      U := W.test.U, V := W.test.V, q := W.test.q, a := W.test.a, endpoints := W.test.endpoints }
  exact ⟨G, funext fun n => by simp only [G, NativePrimeTest.eval,
    RationalFilteredNilmanifold.Niltest.dropTop_eval]⟩

/-- An observable invariant under its top rank subgroup descends to a
controlled quotient at the same degree, with the same evaluations. -/
theorem nativeRankedPrimeTest_rankInvariant_drop (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r X : ℕ} {p : ℝ} (W : NativeRankedPrimeTest s (r + 1) X p), 0 ≤ p →
      (∀ z ∈ W.rank.realSubgroup s (r + 1), ∀ x,
        W.test.test.observable (z • x) = W.test.test.observable x) →
      ∃ G : NativeRankedPrimeTest s r X (((p + 3) ^ (11 : ℕ) + C) ^ C), G.test.eval = W.test.eval := by
  obtain ⟨C, hC, hdrop⟩ := RationalFilteredNilmanifold.DegreeRankStructure.exists_rankInvariant_niltest_budget s
  refine ⟨C, hC, ?_⟩
  intro r X p W hp hinv
  let P := (p + 3) ^ (11 : ℕ)
  have hbase : 1 ≤ p + 3 := by linarith
  have hpP : p ≤ P := (by linarith : p ≤ p + 3).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : (1 : ℕ) ≤ 11))
  have hP : 0 ≤ P := hp.trans hpP
  have hPP : P ≤ (P + C) ^ C := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    exact (by linarith : P ≤ P + C).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ P + C)
        (show 1 ≤ C by omega))
  obtain ⟨n, _, Q, R, _, hQF, hQL, hR, hproj⟩ := W.rank.exists_controlled_lower_rank_quotient hp W.complexity
  let I := W.rank.filtration.layerIdeal s (r + 1)
  let : TopologicalSpace (ℝ ⊗[ℚ] (W.test.L ⧸ I)) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (W.test.L ⧸ I)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (W.test.L ⧸ I)) := realification_moduleTopology_t2 Q.basis
  have h5 : (p + 3) ^ (5 : ℕ) ≤ P := pow_le_pow_right₀ hbase (by decide)
  obtain ⟨T, _, hnorm, hT, _, heval⟩ := hdrop W.rank Q hQF hQL W.test.test P hP
    (W.test.complexity.mono hpP) hR.1 (fun i j => (hproj j i).trans h5) hinv
  let G : NativePrimeTest s X ((P + C) ^ C) :=
    { L := W.test.L ⧸ I, dim := n, model := Q, test := T, complexity := hT
      bound := by rw [hnorm]; exact W.test.bound
      U := W.test.U, V := W.test.V, q := W.test.q, a := W.test.a, endpoints := W.test.endpoints }
  exact ⟨⟨G, R, hR.mono R hPP⟩, funext fun n => by simp only [G, NativePrimeTest.eval, heval]⟩

/-- Iterate a same-degree rank step, allowing an earlier degree drop. The
budget includes at most `r` rank steps from initial rank `r`. -/
theorem nativeRankedPrimeTest_iterate {s X C : ℕ} (hC : 1 ≤ C) {P B : ℝ} (hP : 2 ≤ P)
    (w : ℤ → ℝ)
    (hstep : ∀ r < s + 1, ∀ p : ℝ, P ≤ p → p ^ C ≤ B →
      ∀ W : NativeRankedPrimeTest (s + 1) (r + 1) X p,
        Real.exp (-p) < intervalCorrelation X w W.test.eval →
        (∃ G : NativeRankedPrimeTest (s + 1) r X (p ^ C),
          Real.exp (-(p ^ C)) < intervalCorrelation X w G.test.eval) ∨
        (∃ G : NativePrimeTest s X (p ^ C), Real.exp (-(p ^ C)) < intervalCorrelation X w G.eval)) :
    ∀ r ≤ s + 1, ∀ p : ℝ, P ≤ p → p ^ (C ^ r) ≤ B →
      ∀ W : NativeRankedPrimeTest (s + 1) r X p,
        Real.exp (-p) < intervalCorrelation X w W.test.eval →
        ∃ G : NativePrimeTest s X (p ^ (C ^ r)),
          Real.exp (-(p ^ (C ^ r))) < intervalCorrelation X w G.eval := by
  intro r
  induction r with
  | zero =>
    intro _ p _ _ W hcorr
    obtain ⟨G, hG⟩ := nativeRankedPrimeTest_zero_drop W
    let G' : NativePrimeTest s X (p ^ (C ^ 0)) :=
      { G with complexity := G.complexity.mono (by rw [pow_zero, pow_one]) }
    refine ⟨G', ?_⟩
    change Real.exp (-(p ^ (C ^ 0))) < intervalCorrelation X w G.eval
    simpa only [pow_zero, pow_one, hG] using hcorr
  | succ r ih =>
    intro hr p hp hB W hcorr
    have hrlt : r < s + 1 := by omega
    let q := p ^ C
    have hp1 : 1 ≤ p := (by norm_num : (1 : ℝ) ≤ 2).trans (hP.trans hp)
    have hpq : p ≤ q := by simpa only [q, pow_one] using pow_le_pow_right₀ hp1 hC
    have hq1 : 1 ≤ q := hp1.trans hpq
    have hbudget : q ^ (C ^ r) = p ^ (C ^ (r + 1)) := by
      dsimp only [q]
      rw [← pow_mul, pow_succ, Nat.mul_comm C]
    have hqle : q ≤ p ^ (C ^ (r + 1)) := by
      rw [← hbudget]
      simpa only [pow_one] using pow_le_pow_right₀ hq1 (one_le_pow₀ hC)
    rcases hstep r hrlt p hp (hqle.trans hB) W hcorr with hRank | hDegree
    · obtain ⟨V, hV⟩ := hRank
      have hqB : q ^ (C ^ r) ≤ B := hbudget.le.trans hB
      obtain ⟨G, hG⟩ := ih hrlt.le q (hp.trans hpq) hqB V hV
      let G' : NativePrimeTest s X (p ^ (C ^ (r + 1))) :=
        { G with complexity := G.complexity.mono hbudget.le }
      refine ⟨G', ?_⟩
      change Real.exp (-(p ^ (C ^ (r + 1)))) < intervalCorrelation X w G.eval
      rwa [← hbudget]
    · obtain ⟨G, hG⟩ := hDegree
      let G' : NativePrimeTest s X (p ^ (C ^ (r + 1))) :=
        { G with complexity := G.complexity.mono hqle }
      exact ⟨G', (Real.exp_le_exp.mpr (neg_le_neg hqle)).trans_lt hG⟩

/-- A uniform one-rank drop suffices at each positive degree and rank. -/
def NativePrimeRankStepDescent (S : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in atTop,
    ∀ k < S, ∀ r < k + 1, ∀ p : ℝ,
      max 2 (Real.log (Real.log (X : ℝ))) ≤ p → p ^ C ≤ Real.log (X : ℝ) ^ b →
      ∀ W : NativeRankedPrimeTest (k + 1) (r + 1) X p,
        Real.exp (-p) < intervalCorrelation X (strictVonMangoldtCramerDifference X) W.test.eval →
        (∃ G : NativeRankedPrimeTest (k + 1) r X (p ^ C),
          Real.exp (-(p ^ C)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G.test.eval) ∨
        (∃ G : NativePrimeTest k X (p ^ C),
          Real.exp (-(p ^ C)) < intervalCorrelation X (strictVonMangoldtCramerDifference X) G.eval)

/-- Initialize canonical rank and iterate to rank zero to obtain ordinary
prime–Cramér step descent. All degrees up to `S` use one power budget. -/
theorem native_prime_step_descent_of_rank_step {S : ℕ} (h : NativePrimeRankStepDescent S) :
    PrimeCramerStepDescent S nativePrimeTests := by
  obtain ⟨C, hC, b, hb, hstep⟩ := h
  choose D hD hinit using fun k : ℕ => nativePrimeTest_init_rank (k + 1)
  let M := 2 + ∑ k ∈ Finset.range S, D k
  let A := (M + 1) * M
  let K := A * C ^ S
  have hM : 2 ≤ M := by dsimp only [M]; omega
  have hMpos : 0 < M := by omega
  have hA : 1 ≤ A := Nat.mul_pos (Nat.succ_pos _) hMpos
  have hK : 1 ≤ K := Nat.mul_pos hA (pow_pos hC _)
  refine ⟨K, hK, b, hb, ?_⟩
  filter_upwards [hstep] with X hstep
  intro k hk p hp hbudget F hF hc
  obtain ⟨W, rfl⟩ := hF
  have hp₂ : 2 ≤ p := (le_max_left _ _).trans hp
  have hp₁ : 1 ≤ p := (by norm_num : (1 : ℝ) ≤ 2).trans hp₂
  have hDM : D k ≤ M := by
    have hsum := Finset.single_le_sum (f := D) (fun i _ => Nat.zero_le (D i)) (Finset.mem_range.mpr hk)
    dsimp only [M]
    omega
  have hM' : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hD' : (0 : ℝ) ≤ D k := Nat.cast_nonneg _
  have hDM' : (D k : ℝ) ≤ M := by exact_mod_cast hDM
  have hconst : ((M + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast Nat.succ_le_of_lt M.lt_two_pow_self
  let q := p ^ A
  have hpq : p ≤ q := by simpa only [q, pow_one] using pow_le_pow_right₀ hp₁ hA
  have hinitial : (p + (D k : ℝ)) ^ (D k) ≤ q := by
    calc
      _ ≤ (p + (M : ℝ)) ^ (D k) :=
        pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hDM') _
      _ ≤ (p + (M : ℝ)) ^ M := pow_le_pow_right₀ (by linarith) hDM
      _ ≤ (p ^ (M + 1)) ^ M := by
        apply pow_le_pow_left₀ (by positivity)
        calc
          _ ≤ ((M + 1 : ℕ) : ℝ) * p := by
            push_cast
            nlinarith only [mul_nonneg hM' (sub_nonneg.mpr hp₁)]
          _ ≤ (2 : ℝ) ^ M * p := mul_le_mul_of_nonneg_right hconst (by positivity)
          _ ≤ _ := by
            rw [pow_succ]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hp₂ M) (by positivity)
      _ = q := by simp only [q, A, pow_mul]
  obtain ⟨V₀, hV₀⟩ := hinit k W (by linarith)
  let V : NativeRankedPrimeTest (k + 1) (k + 1) X q :=
    ⟨{ V₀.test with complexity := V₀.test.complexity.mono hinitial }, V₀.rank,
      V₀.complexity.mono V₀.rank hinitial⟩
  have hV : V.test.eval = W.eval := hV₀
  have hqB : q ^ (C ^ (k + 1)) ≤ p ^ K := by
    dsimp only [q, K]
    rw [← pow_mul]
    exact pow_le_pow_right₀ hp₁ (Nat.mul_le_mul_left A
      (Nat.pow_le_pow_right (by omega) (Nat.succ_le_of_lt hk)))
  obtain ⟨G, hG⟩ := nativeRankedPrimeTest_iterate hC (le_max_left 2 (Real.log (Real.log (X : ℝ))))
    (strictVonMangoldtCramerDifference X) (hstep k hk) (k + 1) le_rfl q (hp.trans hpq)
    (hqB.trans hbudget) V (by rw [hV]; exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans_lt hc)
  let G' : NativePrimeTest k X (p ^ K) := { G with complexity := G.complexity.mono hqB }
  exact ⟨G'.eval, ⟨G', rfl⟩, (Real.exp_le_exp.mpr (neg_le_neg hqB)).trans_lt hG⟩

end PrimeUniformity

#print axioms PrimeUniformity.nativePrimeTest_init_rank
#print axioms PrimeUniformity.nativeRankedPrimeTest_zero_drop
#print axioms PrimeUniformity.nativeRankedPrimeTest_rankInvariant_drop
#print axioms PrimeUniformity.nativeRankedPrimeTest_iterate
#print axioms PrimeUniformity.native_prime_step_descent_of_rank_step
