import UpstreamNativePrimeTests
import PrimeUniformity.NilsequenceFreezing
import OAI.Combinatorics.Progressions.Estimates.NativeOrbitFreezing

namespace PrimeUniformity

open OAI.Erdos3
open Module RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativePrimeTest.lie NativePrimeTest.algebra
  NativePrimeTest.topology NativePrimeTest.topologicalAdd
  NativePrimeTest.continuousSMul NativePrimeTest.hausdorff

/-- A successful freezing approximation on the cells of a progression
retains a correlation on one refined progression. The representative is
chosen inside that cell, so it has the rational phase of every point there. -/
theorem exists_frozen_progression_correlation {X U V Q r P B : ℕ}
    (hX : 0 < X) (hUV : U ≤ V) (hVX : V ≤ X) (hr : r < Q) (hP : 0 < P) (hB : 0 < B)
    (w : ℤ → ℝ) (F : ℤ → ℂ) (frozen : ℕ → ℤ → ℂ) {M ε : ℝ} (hε : 0 ≤ ε) :
    let A := (Finset.Ioc U V).filter (fun n => n % Q = r)
    let original := intervalCorrelation X w (fun n => if n ∈ residueSlice ((U : ℤ) + 1)
      ((V - U : ℕ) : ℤ) (r : ZMod Q) then F n else 0)
    (∑ n ∈ A, |w (n : ℤ)|) ≤ (X : ℝ) * M →
    (∀ n ∈ A, ∀ z ∈ A, n % P = z % P → |(n : ℝ) - (z : ℝ)| ≤ B →
      ‖F (n : ℤ) - frozen z (n : ℤ)‖ ≤ ε) →
    ε * M < original →
    ∃ z ∈ A, ∃ a b c : ℕ, a ≤ b ∧ b ≤ X ∧ c < Q * P ∧
      original ≤ ε * M + (↑((Q * P) * ((V - U) / B + 1)) : ℝ) *
        intervalCorrelation X w (fun n => if n ∈ residueSlice ((a : ℤ) + 1)
          ((b - a : ℕ) : ℤ) (c : ZMod (Q * P)) then frozen z n else 0) := by
  classical
  intro A original hw hfreeze hlarge
  let m := Q * P
  let label (n : ℕ) := (n % m, (n - (U + 1)) / B)
  let T := Finset.range m ×ˢ Finset.range ((V - U) / B + 1)
  let Cell (i : ℕ × ℕ) := A.filter (fun n => label n = i)
  let anchor (i : ℕ × ℕ) := if h : (Cell i).Nonempty then h.choose else 0
  let a (j : ℕ) := U + j * B
  let b (j : ℕ) := min V (a j + B)
  have hm : 0 < m := Nat.mul_pos (Nat.zero_lt_of_lt hr) hP
  have hX' : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have hT : T.Nonempty := ⟨(0, 0), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hm, Finset.mem_range.mpr (Nat.succ_pos _)⟩⟩
  have hmaps (n : ℕ) (hn : n ∈ A) : label n ∈ T := by
    have hnV := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hm), Finset.mem_range.mpr ?_⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : n - (U + 1) ≤ V - U))
  have hanchor (i : ℕ × ℕ) (hi : (Cell i).Nonempty) : anchor i ∈ Cell i := by
    rw [show anchor i = hi.choose by simp only [anchor, dite_eq_left hi]]
    exact hi.choose_spec
  have hblock {n j : ℕ} (hn : U < n) :
      (n - (U + 1)) / B = j ↔ a j < n ∧ n ≤ a j + B := by
    rw [Nat.div_eq_iff hB]
    dsimp [a]
    omega
  have hcell {n : ℕ} {i : ℕ × ℕ} (hn : n ∈ Cell i) :
      n ∈ A ∧ n % m = i.1 ∧ n ∈ Finset.Ioc (a i.2) (b i.2) := by
    obtain ⟨hnA, hnI⟩ := Finset.mem_filter.mp hn
    have hmemb := Finset.mem_Ioc.mp (Finset.mem_filter.mp hnA).1
    have hj := (hblock hmemb.1).mp (congrArg Prod.snd hnI)
    exact ⟨hnA, congrArg Prod.fst hnI, Finset.mem_Ioc.mpr ⟨hj.1, le_min hmemb.2 hj.2⟩⟩
  let w' (n : ℕ) : ℂ := w (n : ℤ)
  let u (n : ℕ) := star (F (n : ℤ))
  let v (i : ℕ × ℕ) (n : ℕ) := star (frozen (anchor i) (n : ℤ))
  have happ (n : ℕ) (hn : n ∈ A) : ‖u n - v (label n) n‖ ≤ ε := by
    have hc : n ∈ Cell (label n) := Finset.mem_filter.mpr ⟨hn, rfl⟩
    obtain ⟨hz, hzm, hzb⟩ := hcell (hanchor (label n) ⟨n, hc⟩)
    obtain ⟨_, _, hnb⟩ := hcell hc
    have hmod : n % P = anchor (label n) % P := by
      have hdvd : P ∣ m := dvd_mul_left P Q
      rw [← Nat.mod_mod_of_dvd n hdvd, ← Nat.mod_mod_of_dvd (anchor (label n)) hdvd, hzm]
    have hn' := Finset.mem_Ioc.mp hnb
    have hz' := Finset.mem_Ioc.mp hzb
    have hnV := hn'.2.trans (min_le_right _ _)
    have hzV := hz'.2.trans (min_le_right _ _)
    have hd : |(n : ℝ) - (anchor (label n) : ℝ)| ≤ B := by
      apply abs_le.mpr
      have h1 : n ≤ anchor (label n) + B := by omega
      have h2 : anchor (label n) ≤ n + B := by omega
      have h1' : (n : ℝ) ≤ (anchor (label n) : ℝ) + B := by exact_mod_cast h1
      have h2' : (anchor (label n) : ℝ) ≤ (n : ℝ) + B := by exact_mod_cast h2
      exact ⟨by linarith, by linarith⟩
    change ‖star (F (n : ℤ)) - star (frozen (anchor (label n)) (n : ℤ))‖ ≤ ε
    rw [← star_sub, norm_star]
    exact hfreeze n hn _ hz hmod hd
  let sumOriginal := ‖∑ n ∈ A, w' n * u n‖
  have heq : original = sumOriginal / (X : ℝ) :=
    intervalCorrelation_residue_mask hUV hVX hr w F
  have herror : ε * (∑ n ∈ A, ‖w' n‖) ≤ ε * M * (X : ℝ) := by
    calc
      _ ≤ ε * ((X : ℝ) * M) := by
        apply mul_le_mul_of_nonneg_left _ hε
        simpa only [w', Complex.norm_real, Real.norm_eq_abs] using hw
      _ = _ := by ring
  obtain ⟨i, hi, hret⟩ := exists_large_frozen_piece A T hT label hmaps w' u v happ
    (show sumOriginal ≤ sumOriginal from le_rfl)
  have hex : (Cell i).Nonempty := by
    by_contra! hempty
    have hzero : (∑ n ∈ Cell i, w' n * v i n) = 0 := by
      rw [hempty, Finset.sum_empty]
    have hupper : sumOriginal ≤ ε * M * (X : ℝ) := by
      change sumOriginal ≤ ε * (∑ n ∈ A, ‖w' n‖) + (T.card : ℝ) * ‖∑ n ∈ Cell i, w' n * v i n‖ at hret
      rw [hzero, norm_zero, mul_zero, add_zero] at hret
      exact hret.trans herror
    apply not_le_of_gt hlarge
    rw [heq]
    exact (div_le_iff₀ hX').mpr hupper
  obtain ⟨hz, hzm, hzb⟩ := hcell (hanchor i hex)
  have hz' := Finset.mem_Ioc.mp hzb
  have hab : a i.2 ≤ b i.2 := hz'.1.le.trans hz'.2
  have hbX : b i.2 ≤ X := (min_le_left _ _).trans hVX
  have hc : i.1 < m := Finset.mem_range.mp (Finset.mem_product.mp hi).1
  have hmodz : (anchor i) % Q = r := (Finset.mem_filter.mp hz).2
  have hcell_eq : Cell i = (Finset.Ioc (a i.2) (b i.2)).filter (fun n => n % m = i.1) := by
    ext n
    constructor
    · exact fun hn => Finset.mem_filter.mpr ⟨(hcell hn).2.2, (hcell hn).2.1⟩
    · intro hn
      obtain ⟨hnb, hnm⟩ := Finset.mem_filter.mp hn
      have hnb' := Finset.mem_Ioc.mp hnb
      have hU : U < n := lt_of_le_of_lt (Nat.le_add_right _ _) hnb'.1
      have hV : n ≤ V := hnb'.2.trans (min_le_left _ _)
      have hQmod : n % Q = r := by
        have hdvd : Q ∣ m := dvd_mul_right Q P
        rw [← Nat.mod_mod_of_dvd n hdvd, hnm, ← hzm, Nat.mod_mod_of_dvd _ hdvd, hmodz]
      have hnj := (hblock hU).mpr ⟨hnb'.1, hnb'.2.trans (min_le_right _ _)⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hU, hV⟩, hQmod⟩,
        Prod.ext hnm hnj⟩
  refine ⟨anchor i, hz, a i.2, b i.2, i.1, hab, hbX, hc, ?_⟩
  let new := intervalCorrelation X w (fun n => if n ∈ residueSlice ((a i.2 : ℤ) + 1)
    ((b i.2 - a i.2 : ℕ) : ℤ) (i.1 : ZMod m) then frozen (anchor i) n else 0)
  have hnew : new * (X : ℝ) = ‖∑ n ∈ Cell i, w' n * v i n‖ := by
    rw [show new = _ from intervalCorrelation_residue_mask hab hbX hc w (frozen (anchor i)),
      div_mul_cancel₀ _ hX'.ne', hcell_eq]
  change sumOriginal ≤ ε * (∑ n ∈ A, ‖w' n‖) + (T.card : ℝ) * ‖∑ n ∈ Cell i, w' n * v i n‖ at hret
  rw [← hnew] at hret
  rw [heq]
  apply (div_le_iff₀ hX').mpr
  have hbound := hret.trans (add_le_add herror le_rfl)
  have hTcard : T.card = m * ((V - U) / B + 1) := by simp [T, Finset.card_product]
  rw [hTcard] at hbound
  simpa only [m, new, add_mul, mul_assoc] using hbound

/-- Apply the upstream anchored freezing estimate to normalized factors.
The retained progression carries an actual lower-step native test when
the fast orbit's top subgroup maps into the kernel of the vertical mode. -/
theorem nativePrimeTest_corr_of_normalized_factors (s k : ℕ) :
    ∃ C K : ℕ, 2 ≤ C ∧ 2 ≤ K ∧
      ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
        [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
        {d X : ℕ} {p : ℝ} (hX : 0 < X) (hp : 1 ≤ p)
        (W : NativePrimeTest (s + 1) X p)
        (D : RationalFilteredNilmanifold L (s + 1) d) (hD : D.GeometryComplexityLE p)
        (φ : L →ₗ⁅ℚ⁆ W.L)
        (hφ : ∀ i j, rationalLogHeight (W.model.basis.repr (φ (D.basis j)) i) ≤ p)
        (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (η : W.L →ₗ[ℚ] ℚ)
        (hvertical : ∀ z ∈ W.model.filtration.realification.subgroup (s + 1), ∀ x,
          W.test.observable (z • x) =
            CircleFourier.character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
              W.test.observable x)
        (q : ℕ) (hq : 0 < q) (hqp : (q : ℝ) ≤ Real.exp p)
        (E m R : (W.model.filtration.realification.adaptedPolynomialFiltration
          (fun _ : Unit => 1)).Group)
        (κ : W.model.RealGroup) (hκ : κ ∈ W.model.realLattice)
        (hprod : E * m * R * W.model.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ =
          ⟨⟨W.test.orbit.log, W.test.orbit.property⟩⟩)
        (hgrid : W.model.filtration.PolynomialRationalGrid W.model.basis (fun _ => 1) q R)
        (hslow : W.model.filtration.PolynomialSlowBound W.model.basis (fun _ => 1)
          (fun _ => (X : ℝ)) (Real.exp ((p + 2) ^ k)) E),
        let Φ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := W.model.filtration.lowerCentralSeries_eq_bot) φ
        (∀ n : ℤ, Φ (D.filtration.realification.polynomialOrbitEval _ (fun _ => n) g) =
          W.model.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun _ => (n : ℝ)) m) →
        (∀ z ∈ D.filtration.realification.subgroup (s + 1),
          Φ z ∈ W.model.filtration.realification.subgroup (s + 1) ∧
            realifyFunctional η (Φ z).coord = 0) →
        ∀ (w : ℤ → ℝ) (M : ℝ) (B : ℕ), 0 < B →
          (∑ n ∈ (Finset.Ioc W.U W.V).filter (fun n => n % W.q = W.a.val),
            |w (n : ℤ)|) ≤ (X : ℝ) * M →
          let ε := Real.exp ((p + 2) ^ C) * ((B : ℝ) / (X : ℝ))
          ε * M < intervalCorrelation X w W.eval →
          ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
            ∃ G : NativePrimeTest s X ((p + K) ^ K),
              intervalCorrelation X w W.eval ≤ ε * M +
                (↑((W.q * P) * ((W.V - W.U) / B + 1)) : ℝ) * intervalCorrelation X w G.eval := by
  obtain ⟨C, hC, hFreeze⟩ := RationalFilteredNilmanifold.Niltest.exists_anchored_factor_freezing (s + 1) k
  obtain ⟨K, hK, hBuild⟩ := nativePrimeTest_of_frozen_orbit s C
  refine ⟨C, K, hC, hK, ?_⟩
  intro L _ _ _ _ _ _ d X p hX hp W D hD φ hφ g η hvertical q hq hqp E m R κ hκ hprod
    hgrid hslow Φ hfast htop w M B hB hw ε hlarge
  have hp₀ : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 1).trans hp
  have hX' : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have hσ : (Fintype.card Unit : ℝ) ≤ p := by simpa using hp
  obtain ⟨P, hP, hPbound, hanchored⟩ := hFreeze W.model (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) p hp₀ W.complexity.1 hσ q hq hqp
  let left (z : ℕ) := W.model.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun _ => (z : ℝ)) E
  let right (z : ℕ) := W.model.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun _ => (z : ℝ)) R
  let frozen (z : ℕ) (n : ℤ) := W.test.observable (QuotientGroup.mk
    (left z * Φ (D.filtration.realification.polynomialOrbitEval _ (fun _ => n) g) * right z))
  let A := (Finset.Ioc W.U W.V).filter (fun n => n % W.q = W.a.val)
  have hAX (n : ℕ) (hn : n ∈ A) : n ≤ X :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2.trans W.endpoints.2.1
  have hIntAbs (n : ℕ) (hnX : n ≤ X) : |((n : ℤ) : ℝ)| ≤ (X : ℝ) := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
    exact_mod_cast hnX
  have hdata (z : ℕ) (hz : z ∈ A) := hanchored W.test W.complexity E m R κ hκ hprod hgrid
    (fun _ => (X : ℝ)) (fun _ => hX') hslow (fun _ => (z : ℤ))
    (fun _ => hIntAbs z (hAX z hz))
  have hfreeze (n : ℕ) (hn : n ∈ A) (z : ℕ) (hz : z ∈ A)
      (hmod : n % P = z % P) (hclose : |(n : ℝ) - (z : ℝ)| ≤ (B : ℝ)) :
      ‖W.test.eval (fun _ => (n : ℤ)) - frozen z (n : ℤ)‖ ≤ ε := by
    have hdvd : (P : ℤ) ∣ (n : ℤ) - (z : ℤ) := (show Nat.ModEq P z n from hmod.symm).dvd
    let δ := (B : ℝ) / (X : ℝ)
    have hδ : 0 ≤ δ := div_nonneg (Nat.cast_nonneg B) hX'.le
    have hscale : (X : ℝ) * δ = (B : ℝ) := by
      dsimp only [δ]
      rw [mul_comm, div_mul_cancel₀ _ hX'.ne']
    have hclose' : |((n : ℤ) : ℝ) - ((z : ℤ) : ℝ)| ≤ (X : ℝ) * δ := by
      simpa only [Int.cast_natCast, hscale] using hclose
    have he := (hdata z hz).2.2 (fun _ => (n : ℤ)) δ hδ (fun _ => hIntAbs n (hAX n hn))
      (fun _ => hdvd) (fun _ => hclose')
    simpa only [frozen, left, right, hfast, Int.cast_natCast] using he
  have hqW : 0 < W.q := W.endpoints.2.2
  let : NeZero W.q := ⟨hqW.ne'⟩
  have hrW : W.a.val < W.q := ZMod.val_lt W.a
  have hOrig (n : ℤ) : (if n ∈ residueSlice ((W.U : ℤ) + 1) ((W.V - W.U : ℕ) : ℤ)
      (W.a.val : ZMod W.q) then W.test.eval (fun _ => n) else 0) = W.eval n := by
    simp only [ZMod.natCast_zmod_val, NativePrimeTest.eval]
  obtain ⟨z, hz, a, b, c, hab, hbX, hc, hcorr⟩ := exists_frozen_progression_correlation
    hX W.endpoints.1 W.endpoints.2.1 hrW hP hB w (fun n => W.test.eval (fun _ => n)) frozen
      (by positivity : 0 ≤ ε) hw hfreeze (by simpa only [hOrig] using hlarge)
  have hfrozen_inv (z' : D.RealGroup) (hz' : z' ∈ D.filtration.realification.subgroup (s + 1))
      (x : D.RealGroup) :
      W.test.observable (QuotientGroup.mk (left z * Φ (z' * x) * right z)) =
        W.test.observable (QuotientGroup.mk (left z * Φ x * right z)) := by
    obtain ⟨hmem, hzero⟩ := htop z' hz'
    have hcomm := W.model.filtration.realification.top_commutes _ hmem (left z)
    have hmul : left z * Φ (z' * x) * right z = Φ z' * (left z * Φ x * right z) := by
      rw [map_mul, ← mul_assoc (left z) (Φ z') (Φ x), hcomm.eq.symm]
      simp only [mul_assoc]
    rw [hmul]
    change W.test.observable (Φ z' • (QuotientGroup.mk (left z * Φ x * right z) : W.model.Space)) = _
    rw [hvertical _ hmem, hzero]
    simp
  obtain ⟨G, hG⟩ := hBuild D W φ g hp₀ hD hφ q hq hqp (left z) (right z)
    (by simpa only [left, Int.cast_natCast] using (hdata z hz).1)
    (by simpa only [right, Int.cast_natCast] using (hdata z hz).2.1)
    hfrozen_inv a b (W.q * P) hab hbX (Nat.mul_pos hqW hP) (c : ZMod (W.q * P))
  have hEval : G.eval = fun n => if n ∈ residueSlice ((a : ℤ) + 1)
      ((b - a : ℕ) : ℤ) (c : ZMod (W.q * P)) then frozen z n else 0 := funext hG
  exact ⟨P, hP, hPbound, G, by simpa only [hOrig, ← hEval] using hcorr⟩


end PrimeUniformity
