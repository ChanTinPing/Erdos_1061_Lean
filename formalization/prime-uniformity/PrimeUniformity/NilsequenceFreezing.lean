module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod

public section

namespace PrimeUniformity

open scoped BigOperators NNReal

/-- Pointwise freezing at accuracy `ε` changes the total weighted correlation
by at most `ε` times the total absolute weight. -/
theorem norm_weighted_correlation_sub_le
    {α : Type*} (s : Finset α) (w u v : α → ℂ) {ε : ℝ}
    (happrox : ∀ a ∈ s, ‖u a - v a‖ ≤ ε) :
    ‖(∑ a ∈ s, w a * u a) - (∑ a ∈ s, w a * v a)‖ ≤
      ε * ∑ a ∈ s, ‖w a‖ := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    _ ≤ ∑ a ∈ s, ‖w a * u a - w a * v a‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun a ha => by
      rw [← mul_sub, norm_mul, mul_comm ε]
      exact mul_le_mul_of_nonneg_left (happrox a ha) (norm_nonneg _))

/-- Partition the finite correlation by `label` and freeze separately on each
piece. One piece retains at least the residual budget divided by the number
of pieces. The inequality remains valid when the approximation error
already exceeds the original budget. -/
theorem exists_large_frozen_piece {α κ : Type*} [DecidableEq κ]
    (s : Finset α) (T : Finset κ) (hT : T.Nonempty)
    (label : α → κ) (hlabel : ∀ a ∈ s, label a ∈ T)
    (w u : α → ℂ) (v : κ → α → ℂ) {ε H : ℝ}
    (happrox : ∀ a ∈ s, ‖u a - v (label a) a‖ ≤ ε)
    (hlarge : H ≤ ‖∑ a ∈ s, w a * u a‖) :
    ∃ j ∈ T, H ≤ ε * (∑ a ∈ s, ‖w a‖) +
      (T.card : ℝ) * ‖∑ a ∈ s.filter (fun a => label a = j), w a * v j a‖ := by
  let c (j : κ) : ℂ := ∑ a ∈ s.filter (fun a => label a = j), w a * v j a
  have hsplit : (∑ a ∈ s, w a * v (label a) a) = ∑ j ∈ T, c j := by
    rw [← Finset.sum_fiberwise_of_maps_to hlabel (fun a => w a * v (label a) a)]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a ha
    rw [(Finset.mem_filter.mp ha).2]
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image T (fun j => ‖c j‖) hT
  refine ⟨j, hj, hlarge.trans ?_⟩
  calc
    _ = ‖((∑ a ∈ s, w a * u a) - (∑ a ∈ s, w a * v (label a) a)) +
        (∑ a ∈ s, w a * v (label a) a)‖ := by rw [sub_add_cancel]
    _ ≤ ‖(∑ a ∈ s, w a * u a) - (∑ a ∈ s, w a * v (label a) a)‖ +
        ‖∑ a ∈ s, w a * v (label a) a‖ := norm_add_le _ _
    _ ≤ ε * (∑ a ∈ s, ‖w a‖) + ∑ j ∈ T, ‖c j‖ := by
      apply add_le_add (norm_weighted_correlation_sub_le s w u (fun a => v (label a) a) happrox)
      rw [hsplit]
      exact norm_sum_le _ _
    _ ≤ ε * (∑ a ∈ s, ‖w a‖) + ∑ _i ∈ T, ‖c j‖ :=
      add_le_add_right (Finset.sum_le_sum hmax) _
    _ = _ := by simp [c, nsmul_eq_mul]

/-- A slowly varying parameter may be replaced by a chosen anchor on each
piece. The approximation error uses the observable's Lipschitz constant
and the maximal distance to the anchors. -/
theorem exists_large_piece_after_freezing_smooth
    {α κ E : Type*} [DecidableEq κ] [PseudoMetricSpace E]
    (s : Finset α) (T : Finset κ) (hT : T.Nonempty)
    (label : α → κ) (hlabel : ∀ a ∈ s, label a ∈ T)
    (w : α → ℂ) (F : E → α → ℂ) (smooth : α → E) (anchor : κ → E)
    {L : ℝ≥0} {r H : ℝ}
    (hF : ∀ a ∈ s, LipschitzWith L (fun x => F x a))
    (hsmooth : ∀ a ∈ s, dist (smooth a) (anchor (label a)) ≤ r)
    (hlarge : H ≤ ‖∑ a ∈ s, w a * F (smooth a) a‖) :
    ∃ j ∈ T, H ≤ (L : ℝ) * r * (∑ a ∈ s, ‖w a‖) +
      (T.card : ℝ) * ‖∑ a ∈ s.filter (fun a => label a = j), w a * F (anchor j) a‖ := by
  apply exists_large_frozen_piece s T hT label hlabel w (fun a => F (smooth a) a)
    (fun j a => F (anchor j) a) _ hlarge
  intro a ha
  rw [← dist_eq_norm]
  exact (hF a ha).dist_le_mul_of_le (hsmooth a ha)

/-- Freeze simultaneously on a short interval and on one residue class
modulo the period of the rational factor. The selected support is again
the intersection of an integer interval and a single residue class. -/
theorem exists_large_frozen_progression_piece {E : Type*} [PseudoMetricSpace E]
    (a b Q B : ℕ) (hQ : 0 < Q) (hB : 0 < B)
    (w : ℕ → ℂ) (F : E → ℕ → ℂ) (smooth : ℕ → E) {L : ℝ≥0} {r H : ℝ}
    (hF : ∀ n ∈ Finset.Icc a b, LipschitzWith L (fun x => F x n))
    (hsmooth : ∀ n ∈ Finset.Icc a b, dist (smooth n) (smooth (a + ((n - a) / B) * B)) ≤ r)
    (hlarge : H ≤ ‖∑ n ∈ Finset.Icc a b, w n * F (smooth n) n‖) :
    ∃ c < Q, ∃ j ≤ (b - a) / B,
      H ≤ (L : ℝ) * r * (∑ n ∈ Finset.Icc a b, ‖w n‖) +
        (↑(Q * ((b - a) / B + 1)) : ℝ) *
          ‖∑ n ∈ (Finset.Icc (a + j * B) (min b (a + j * B + B - 1))).filter
                (fun n => n % Q = c),
            w n * F (smooth (a + j * B)) n‖ := by
  let label (n : ℕ) := (n % Q, (n - a) / B)
  let T := Finset.range Q ×ˢ Finset.range ((b - a) / B + 1)
  have hT : T.Nonempty := ⟨(0, 0), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hQ, Finset.mem_range.mpr (Nat.succ_pos _)⟩⟩
  have hlabel (n : ℕ) (hn : n ∈ Finset.Icc a b) : label n ∈ T :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hQ),
      Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right (Nat.sub_le_sub_right (Finset.mem_Icc.mp hn).2 _)))⟩
  obtain ⟨⟨c, j⟩, hcj, hbound⟩ := exists_large_piece_after_freezing_smooth
    (Finset.Icc a b) T hT label hlabel w F smooth (fun x => smooth (a + x.2 * B))
    hF hsmooth hlarge
  obtain ⟨hc, hj⟩ := Finset.mem_product.mp hcj
  refine ⟨c, Finset.mem_range.mp hc, j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), ?_⟩
  have hfiber : (Finset.Icc a b).filter (fun n => label n = (c, j)) =
      (Finset.Icc (a + j * B) (min b (a + j * B + B - 1))).filter (fun n => n % Q = c) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, label, Prod.mk.injEq,
      Nat.div_eq_iff hB, le_min_iff]
    omega
  rwa [hfiber, Finset.card_product, Finset.card_range, Finset.card_range] at hbound


end PrimeUniformity
