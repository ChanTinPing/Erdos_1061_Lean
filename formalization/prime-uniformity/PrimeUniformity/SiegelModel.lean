module

public import PrimeUniformity.LogSavings
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

@[expose] public section

namespace PrimeUniformity

open Filter

/-- Data entering the exceptional correction. The hypotheses on the character
and its zero belong to the analytic estimates that supply this data. -/
structure SiegelCorrection where
  modulus : ℕ
  beta : ℝ
  character : ℤ → ℝ

/-- The Siegel model for the von Mangoldt weight on positive integers. -/
noncomputable def siegelWeight (X : ℕ) (exception : Option SiegelCorrection) (n : ℤ) : ℝ :=
  cramerWeight (primeUniformityCutoff X) n *
    match exception with
    | none => 1
    | some e => 1 - (n : ℝ) ^ (e.beta - 1) * e.character n

@[simp] theorem siegelWeight_none (X : ℕ) (n : ℤ) :
    siegelWeight X none n = cramerWeight (primeUniformityCutoff X) n := by
  simp [siegelWeight]

/-- A uniform logarithmic zero gap excludes a zero at the
Tao–Teräväinen threshold whenever its cutoff constant is small enough. -/
theorem not_exceptional_of_uniform_log_gap {q : ℕ} {Q β c c₀ : ℝ}
    (hq : 0 < q) (hqQ : (q : ℝ) ≤ Q) (hQ : 1 < Q) (hβ : β < 1)
    (hc : c₀ ≤ c) (hgap : c ≤ (1 - β) * Real.log (q : ℝ)) :
    ¬ (1 - c₀ / Real.log Q < β) := by
  intro hnear
  have hlog : Real.log (q : ℝ) ≤ Real.log Q :=
    Real.log_le_log (by exact_mod_cast hq) hqQ
  have hlt : (1 - β) * Real.log Q < c₀ :=
    (lt_div_iff₀ (Real.log_pos hQ)).mp (by linarith)
  exact hlt.not_ge (hc.trans (hgap.trans (mul_le_mul_of_nonneg_left hlog (by linarith))))

/-- The integer floor in the Cramér cutoff does not alter the order of its logarithm. -/
theorem eventually_log_primeUniformityCutoff_ge :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ^ (1 / 10 : ℝ) / 2 ≤ Real.log (primeUniformityCutoff X : ℝ) := by
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually_ge_atTop 2] with X hT
  let t := Real.log (X : ℝ) ^ (1 / 10 : ℝ)
  have ht₂ : 2 ≤ t := hT
  have he₂ : 2 ≤ Real.exp t := by
    have he := Real.add_one_le_exp t
    linarith
  have hfloor : Real.exp t < (primeUniformityCutoff X : ℝ) + 1 :=
    Nat.lt_floor_add_one (Real.exp t)
  have hhalf : Real.exp t / 2 ≤ (primeUniformityCutoff X : ℝ) := by linarith
  have hlog := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num)) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlog
  have hlog₂ : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  linarith

/-- The exceptional correction obeys each logarithmic moment bound once its
power saving and the upper and lower bounds on the zero's gap are supplied. -/
theorem intervalMomentBound_siegelCorrection (d A : ℕ)
    (exception : ℕ → Option SiegelCorrection) {Cs cs E : ℝ}
    (hCs : 0 < Cs) (hcs : 0 < cs) (hE : 0 < E)
    (hcorrection : ∀ᶠ X : ℕ in atTop, ∀ e : SiegelCorrection, exception X = some e →
      intervalCubeSum d.succ X (fun n =>
        siegelWeight X (exception X) n - cramerWeight (primeUniformityCutoff X) n) ≤
        (Cs / (e.modulus : ℝ) ^ cs) * intervalCubeSum d.succ X (fun _ => 1))
    (hclose : ∀ᶠ X : ℕ in atTop, ∀ e : SiegelCorrection, exception X = some e →
      1 - e.beta ≤ E / Real.log (primeUniformityCutoff X : ℝ))
    (hsiegel : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 < D ∧ ∀ᶠ X : ℕ in atTop,
      ∀ e : SiegelCorrection, exception X = some e →
        0 < e.modulus ∧ D / (e.modulus : ℝ) ^ ε ≤ 1 - e.beta) :
    IntervalMomentBound d.succ A
      (fun X n => siegelWeight X (exception X) n - cramerWeight (primeUniformityCutoff X) n) := by
  let q (X : ℕ) := (exception X).map SiegelCorrection.modulus
  let gap (X : ℕ) : ℝ := (exception X).elim 0 (fun e => 1 - e.beta)
  have hgrowth : ExceptionalModulusGrowth q := by
    apply exceptionalModulusGrowth_of_gap_bounds q gap (E := 2 * E)
      (s := 1 / 10) (by positivity) (by norm_num)
    · have hlog : ∀ᶠ X : ℕ in atTop, 0 < Real.log (X : ℝ) := by
        filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
        exact Real.log_pos (by exact_mod_cast (show 1 < X from hX))
      filter_upwards [hclose, eventually_log_primeUniformityCutoff_ge, hlog] with X hβ hcut hlog
      intro m hm
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hm
      simp only [gap, he, Option.elim_some]
      refine (hβ e he).trans ?_
      rw [mul_comm (2 : ℝ), ← div_div_eq_mul_div]
      exact div_le_div_of_nonneg_left hE.le (by positivity) hcut
    · intro ε hε
      obtain ⟨D, hD, h⟩ := hsiegel ε hε
      refine ⟨D, hD, ?_⟩
      filter_upwards [h] with X hX
      intro m hm
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hm
      simpa only [gap, he, Option.elim_some] using hX e he
  apply IntervalMomentBound.of_modulus_power_saving (q := q) hCs hcs hgrowth _ A
  filter_upwards [hcorrection] with X hX
  cases he : exception X with
  | none =>
    simp only [he, siegelWeight_none, sub_self, q, Option.map_none, zero_mul]
    simp [intervalCubeSum, cubeProduct_eq_zero_of_vertex d.succ
      (intervalWeight X (fun _ => 0)) _ _ (fun _ => false) (by simp [intervalWeight])]
  | some e =>
    simpa only [q, he, Option.map_some] using hX e he

/-- The quantitative prime estimate follows from the stretched-exponential
prime comparison, the power saving for the exceptional correction and the
lower gap bound for the exceptional zero. -/
theorem gowersUniformityEstimate_of_siegel_bounds (d A : ℕ)
    (exception : ℕ → Option SiegelCorrection)
    {Cp cp Cs cs E : ℝ}
    (hCp : 0 < Cp) (hcp : 0 < cp) (hCs : 0 < Cs) (hcs : 0 < cs) (hE : 0 < E)
    (hprime : ∀ᶠ X : ℕ in atTop,
      intervalCubeSum d.succ X (fun n => primeWeight n - siegelWeight X (exception X) n) ≤
        (Cp * Real.exp (-(Real.log (X : ℝ) ^ cp))) * intervalCubeSum d.succ X (fun _ => 1))
    (hcorrection : ∀ᶠ X : ℕ in atTop, ∀ e : SiegelCorrection, exception X = some e →
      intervalCubeSum d.succ X (fun n =>
        siegelWeight X (exception X) n - cramerWeight (primeUniformityCutoff X) n) ≤
        (Cs / (e.modulus : ℝ) ^ cs) * intervalCubeSum d.succ X (fun _ => 1))
    (hclose : ∀ᶠ X : ℕ in atTop, ∀ e : SiegelCorrection, exception X = some e →
      1 - e.beta ≤ E / Real.log (primeUniformityCutoff X : ℝ))
    (hsiegel : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 < D ∧ ∀ᶠ X : ℕ in atTop,
      ∀ e : SiegelCorrection, exception X = some e →
        0 < e.modulus ∧ D / (e.modulus : ℝ) ^ ε ≤ 1 - e.beta) :
    GowersUniformityEstimate d.succ A := by
  apply gowersUniformityEstimate_of_model_comparisons d A (fun X => siegelWeight X (exception X))
  · exact IntervalMomentBound.of_stretched_exponential hCp hcp hprime A
  · exact intervalMomentBound_siegelCorrection d A exception hCs hcs hE hcorrection hclose hsiegel

end PrimeUniformity
