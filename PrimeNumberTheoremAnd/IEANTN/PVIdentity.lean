import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Batteries.Tactic.ShowUnused

open Real Set MeasureTheory Filter Topology Finset
open scoped NNReal ENNReal

/-!
# Principal value identity

# Key theorems

- pv_exp_div_eq_gamma_add_log_add_integral : ∫ u in (0 : ℝ)..y, ((exp u - 1) / u) = eulerMascheroniConstant + log y + ∫ u in (0 : ℝ)..y, ((exp u - 1) / u)
-/

-- set_option linter.unusedSimpArgs false
-- set_option linter.style.multiGoal false
-- set_option linter.unusedVariables false
-- set_option linter.style.refine false
-- set_option linter.style.setOption false
set_option linter.flexible false
-- set_option linter.style.maxHeartbeats false
-- set_option linter.unnecessarySimpa false

/-! ## Helper lemmas for the principal value identity -/
/-
PROBLEM
The substitution u = -t transforms ∫_{-1/ε}^{-ε} exp(u)/u du to -∫_{ε}^{1/ε} exp(-t)/t dt
PROVIDED SOLUTION
Use the substitution u = -t in the interval integral. Use intervalIntegral.integral_comp_neg or similar. We have ∫_{-1/ε}^{-ε} exp(u)/u du. With the substitution u = -t, du = -dt, the integral becomes ∫_{1/ε}^{ε} exp(-t)/(-t)(-dt) = ∫_{1/ε}^{ε} exp(-t)/t dt = -∫_{ε}^{1/ε} exp(-t)/t dt.
-/
lemma integral_exp_div_neg_eq {ε : ℝ} (hε : 0 < ε) :
    ∫ u in (-1/ε)..(-ε), exp u / u = -(∫ t in ε..(1/ε), exp (-t) / t) := by
  -- Apply the substitution $u = -t$ and adjust the limits of integration accordingly.
  have h_subst : ∫ u in (-1 / ε)..(-ε), Real.exp u / u = ∫ t in (ε : ℝ)..1 / ε, Real.exp (-t) / (-t) := by
    have h_sub : ∀ a b : ℝ, ∫ u in a..b, Real.exp u / u = ∫ t in (-b)..(-a), Real.exp (-t) / (-t) := by
      norm_num [ ← intervalIntegral.integral_comp_neg ]
    grind;
  simpa [ div_neg ] using h_subst
/-
PROBLEM
Splitting exp(u)/u = (exp(u)-1)/u + 1/u in the interval integral
PROVIDED SOLUTION
Split exp(u)/u = (exp(u)-1)/u + 1/u. Since both functions are integrable on [a,b] (as a > 0, the functions are continuous on [a,b]), we can split the integral. The integral of 1/u from a to b is log(b) - log(a). Use intervalIntegral.integral_add and the integral of 1/u.
-/
lemma integral_exp_div_split {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, exp u / u = (∫ u in a..b, (exp u - 1) / u) + (log b - log a) := by
  simp +decide [ sub_div ];
  rw [ intervalIntegral.integral_sub ];
  · rw [ integral_inv_of_pos, Real.log_div ] <;> linarith;
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div ( Real.continuous_exp.continuousAt ) continuousAt_id <| by linarith [ Set.mem_Icc.mp <| by simpa [ hab ] using hu ] ) ..;
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ continuousAt_id ( by cases Set.mem_uIcc.mp hx <;> linarith )
/-
PROBLEM
The function (1 - exp(-t))/t is integrable on (0, 1]
PROVIDED SOLUTION
The function (1 - exp(-t))/t is bounded by 1 on (0,1] since 1 - exp(-t) ≤ t for t ≥ 0 (equivalently, exp(-t) ≥ 1 - t). Since it's bounded and measurable on a bounded interval, it's integrable. Use Integrable.mono' with the constant function 1.
-/
lemma integrableOn_one_sub_exp_neg_div :
    IntegrableOn (fun t => (1 - exp (-t)) / t) (Ioc 0 1) := by
  -- We'll use the fact that \( \frac{1 - e^{-t}}{t} \) is bounded above by 1 on the interval (0, 1].
  have h_bound : ∀ t ∈ Set.Ioc 0 1, (1 - Real.exp (-t)) / t ≤ 1 := by
    exact fun t ht => by rw [ div_le_iff₀ ht.1 ] ; linarith [ Real.add_one_le_exp ( -t ) ] ;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  exacts [ fun t => 1, by norm_num, by exact Measurable.aestronglyMeasurable ( by exact Measurable.div ( measurable_const.sub ( Real.continuous_exp.measurable.comp ( measurable_neg ) ) ) measurable_id' ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun t ht => by rw [ Real.norm_of_nonneg ( div_nonneg ( sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by linarith [ ht.1, ht.2 ] ) ht.1.le ) ] ; exact h_bound t ht ]
/-
PROBLEM
The function exp(-t)/t is integrable on (1, ∞)
PROVIDED SOLUTION
exp(-t)/t ≤ exp(-t) for t ≥ 1, and exp(-t) is integrable on (1,∞). Use Integrable.mono' with exp(-t) as the bound.
-/
lemma integrableOn_exp_neg_div_Ioi :
    IntegrableOn (fun t => exp (-t) / t) (Ioi 1) := by
  -- We'll use the fact that $\frac{e^{-t}}{t}$ is integrable on $(1, \infty)$ because it is bounded and continuous.
  have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 1) := by
    exact MeasureTheory.IntegrableOn.mono_set ( by exact MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero ) ) ( Set.Ioi_subset_Ioi zero_le_one );
  refine' h_integrable.mono' _ _;
  · exact ContinuousOn.aestronglyMeasurable ( fun t ht => ContinuousAt.continuousWithinAt ( by exact ContinuousAt.div ( ContinuousAt.rexp ( continuousAt_id.neg ) ) continuousAt_id ( by linarith [ ht.out ] ) ) ) measurableSet_Ioi;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.exp_pos _ |> le_of_lt ) ( by linarith [ hx.out ] ) ) ] ; exact div_le_self ( Real.exp_pos _ |> le_of_lt ) ( by linarith [ hx.out ] ) ;
/-
PROBLEM
The function (exp(u)-1)/u is integrable on (0, y] for y > 0
PROVIDED SOLUTION
The function (exp(u)-1)/u is bounded on (0,y]: near 0 it approaches 1 (by L'Hôpital), and on (0,y] it's bounded by exp(y). More precisely, (exp(u)-1)/u ≤ exp(y) for u in (0,y] since exp(u)-1 ≤ u*exp(u) ≤ u*exp(y). Use Integrable.mono' with the constant exp(y).
-/
lemma integrableOn_exp_sub_one_div {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun u => (exp u - 1) / u) (Ioc 0 y) := by
  -- Since $(Real.exp u - 1) / u$ is bounded on $(0, y]$, we can apply the Integrable.mono' lemma.
  have h_bounded : ∀ u ∈ Set.Ioc 0 y, |(Real.exp u - 1) / u| ≤ Real.exp y := by
    norm_num [ abs_div ];
    intro u hu huy; rw [ abs_of_nonneg ( sub_nonneg_of_le ( Real.one_le_exp hu.le ) ), abs_of_nonneg hu.le ] ; rw [ div_le_iff₀ hu ] ; nlinarith [ Real.exp_pos u, Real.exp_le_exp.2 huy, Real.exp_neg u, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos u ) ), Real.add_one_le_exp u, Real.add_one_le_exp ( -u ) ] ;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  exacts [ fun u => Real.exp y, by norm_num, by exact Measurable.aestronglyMeasurable ( by exact Measurable.div ( Real.continuous_exp.measurable.sub measurable_const ) measurable_id' ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun u hu => h_bounded u hu ]
/-
PROBLEM
∫_ε^1 (1-exp(-t))/t dt → ∫_0^1 (1-exp(-t))/t dt as ε → 0+
PROVIDED SOLUTION
The function (1-exp(-t))/t is integrable on (0,1] (by integrableOn_one_sub_exp_neg_div). The interval integral ∫_ε^1 is continuous as a function of ε. As ε → 0+, we get ∫_0^1. Use continuity of the interval integral at the endpoint. Since the function is integrable on (0,1], the interval integral ∫_ε^1 f(t) dt converges to ∫_0^1 f(t) dt as ε → 0+. This can be shown by using intervalIntegral.integral_tendsto or by showing continuity of ε ↦ ∫_ε^1 f and evaluating at 0.
-/
lemma tendsto_integral_one_sub_exp_neg_div :
    Tendsto (fun ε => ∫ t in ε..1, (1 - exp (-t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in (0:ℝ)..1, (1 - exp (-t)) / t)) := by
  -- The function (1 - exp(-t))/t is integrable on (0, 1] by the provided lemma.
  have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => (1 - Real.exp (-t)) / t) (Set.Ioc 0 1) := by
    exact integrableOn_one_sub_exp_neg_div;
  -- The integral of a continuous function over a compact interval is continuous, hence the limit can be passed inside.
  have h_cont : ContinuousOn (fun ε => ∫ t in (ε)..1, (1 - Real.exp (-t)) / t) (Set.Icc 0 1) := by
    have h_cont : ContinuousOn (fun ε => ∫ t in (1 : ℝ)..ε, (1 - Real.exp (-t)) / t) (Set.Icc 0 1) := by
      intro ε hε; apply_rules [ intervalIntegral.continuousWithinAt_primitive ] ; aesop;
      rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ] <;> aesop;
    exact ContinuousOn.congr ( h_cont.neg ) fun x hx => by rw [ ← intervalIntegral.integral_symm ] ;
  have := h_cont 0 ( by norm_num );
  convert this.tendsto.mono_left _ using 2 ; norm_num [ Set.Ioi_subset_Ici_self ];
  exact nhdsWithin_mono _ <| Set.Ioi_subset_Ici_self
/-
PROBLEM
∫_1^{1/ε} exp(-t)/t dt → ∫_1^∞ exp(-t)/t dt as ε → 0+
PROVIDED SOLUTION
exp(-t)/t is integrable on (1,∞) (by integrableOn_exp_neg_div_Ioi). Use intervalIntegral_tendsto_integral_Ioi: as the upper limit goes to ∞, the interval integral converges to the improper integral. Since 1/ε → ∞ as ε → 0+, compose with Tendsto (1/·) (𝓝[>] 0) atTop.
-/
lemma tendsto_integral_exp_neg_div_Ioi :
    Tendsto (fun ε => ∫ t in (1:ℝ)..(1/ε), exp (-t) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in Ioi (1:ℝ), exp (-t) / t)) := by
  -- The function $\frac{\exp(-t)}{t}$ is continuous on $[1, \infty)$ by the properties of the exponential and logarithm functions.
  simp [Real.exp_pos] at * ; have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioi 1) := by
    exact integrableOn_exp_neg_div_Ioi;
  apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
  norm_num [ Filter.Tendsto ]
/-
PROBLEM
∫_ε^y (exp(u)-1)/u du → ∫_0^y (exp(u)-1)/u du as ε → 0+
PROVIDED SOLUTION
Similar to tendsto_integral_one_sub_exp_neg_div. The function (exp(u)-1)/u is integrable on (0,y] (by integrableOn_exp_sub_one_div). The interval integral ∫_ε^y is continuous in ε, and as ε → 0+, converges to ∫_0^y. Use continuity of the antiderivative at the lower endpoint.
-/
lemma tendsto_integral_exp_sub_one_div {y : ℝ} (hy : 0 < y) :
    Tendsto (fun ε => ∫ u in ε..y, (exp u - 1) / u)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ u in (0:ℝ)..y, (exp u - 1) / u)) := by
  -- The function (exp(u)-1)/u is integrable on (0,y].
  have h_integrable : MeasureTheory.IntegrableOn (fun u => (Real.exp u - 1) / u) (Set.Ioc 0 y) := by
    exact integrableOn_exp_sub_one_div hy;
  -- Let's choose any $M > 0$ such that $y < M$.
  obtain ⟨M, hM⟩ : ∃ M > y, True := by
    exact ⟨ y + 1, by linarith, trivial ⟩;
  -- The integral of (exp(u)-1)/u over (0, M) is continuous at 0.
  have h_cont : ContinuousOn (fun ε => ∫ u in ε..y, (Real.exp u - 1) / u) (Set.Icc 0 M) := by
    have h_integrable_M : MeasureTheory.IntegrableOn (fun u => (Real.exp u - 1) / u) (Set.Ioc 0 M) := by
      have h_integrable_M : MeasureTheory.IntegrableOn (fun u => (Real.exp u - 1) / u) (Set.Ioc y M) := by
        exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div ( ContinuousAt.sub ( Real.continuous_exp.continuousAt ) continuousAt_const ) continuousAt_id <| by linarith [ hu.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
      convert h_integrable.union h_integrable_M using 1 ; rw [ Set.Ioc_union_Ioc_eq_Ioc ] <;> linarith;
    have h_cont : ContinuousOn (fun ε => ∫ u in (y)..ε, (Real.exp u - 1) / u) (Set.Icc 0 M) := by
      intro ε hε; apply_rules [ intervalIntegral.continuousWithinAt_primitive ] ; aesop;
      rw [ min_eq_right hy.le, max_eq_right hM.1.le ] ; rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ( by linarith ) ] ; aesop;
    exact ContinuousOn.congr ( h_cont.neg ) fun x hx => by rw [ ← intervalIntegral.integral_symm ] ;
  have := h_cont 0 ⟨ by norm_num, by linarith ⟩;
  convert this.tendsto.mono_left _ using 2;
  norm_num [ nhdsWithin, Filter.mem_inf_principal ];
  exact Filter.eventually_of_mem ( Iio_mem_nhds <| show 0 < M by linarith ) fun x hx => fun hx' => ⟨ le_of_lt hx', le_of_lt hx ⟩

-- set_option maxHeartbeats 1000000 in
lemma eulerMascheroni_eq_integral' :
    eulerMascheroniConstant =
      (∫ t in (0:ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1:ℝ), exp (-t) / t := by
  -- Using the existing Gamma-derivative integral formula, we can write
  have h_gamma_deriv : Real.eulerMascheroniConstant = -∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t := by
    have h_gamma_deriv : deriv Real.Gamma 1 = ∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t := by
      let I : ℂ := ∫ t : ℝ in Ioi 0, t ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t))
      have h_complex_gamma : HasDerivAt Complex.Gamma I (1 : ℂ) := by
        refine Complex.hasDerivAt_GammaIntegral (by simp) |>.congr_of_eventuallyEq ?_
        have h_open : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt (by fun_prop) (by fun_prop)
        filter_upwards [h_open.mem_nhds (by simp)] with s hs using (Complex.Gamma_eq_integral hs)
      convert h_complex_gamma.real_of_complex.deriv
      simp [I, mul_comm, ← Complex.ofReal_mul, integral_complex_ofReal, - Complex.ofReal_exp]
    rw [Real.eulerMascheroniConstant_eq_neg_deriv, h_gamma_deriv]
  have h_tail_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.log t) (Set.Ioi 1) := by
    sorry
  have h_tail_div_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioi 1) := by
    sorry
  -- We can split the integral into two parts: from 0 to 1 and from 1 to ∞.
  have h_split : ∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t = (∫ t in Set.Ioc 0 1, Real.exp (-t) * Real.log t) + (∫ t in Set.Ioi 1, Real.exp (-t) * Real.log t) := by
    rw [← MeasureTheory.setIntegral_union] <;> norm_num
    · have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.log t) (Set.Ioc 0 1) := sorry
      refine' h_integrable.norm.mono' _ _
      · exact MeasureTheory.AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable (by continuity)) h_integrable.aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx using by rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _ |> le_of_lt)]; exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr <| by linarith [hx.1, hx.2])
    · exact h_tail_integrable
  -- For the integral from 0 to 1, integration by parts gives the required one-variable identity.
  have h_zero_one : -(∫ t in Set.Ioc 0 1, Real.exp (-t) * Real.log t) = ∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t := by
    have h_trunc : ∀ a ∈ Set.Ioo (0 : ℝ) 1, -(∫ t in a..1, Real.exp (-t) * Real.log t) = (∫ t in a..1, (1 - Real.exp (-t)) / t) + (1 - Real.exp (-a)) * Real.log a := by
      intro a ha
      have h_parts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := 1) (u := Real.log) (v := fun x : ℝ => Real.exp (-x) - 1) (u' := fun x : ℝ => 1 / x) (v' := fun x : ℝ => -Real.exp (-x)) sorry sorry sorry sorry
      calc
        -(∫ t in a..1, Real.exp (-t) * Real.log t) = ∫ t in a..1, Real.log t * (-Real.exp (-t)) := by rw [← intervalIntegral.integral_neg]; refine intervalIntegral.integral_congr fun t ht => by ring
        _ = (∫ t in a..1, (1 - Real.exp (-t)) / t) + (1 - Real.exp (-a)) * Real.log a := by
          rw [h_parts]; simp [Real.log_one, ha.1.ne']; rw [add_comm]; congr 1
          sorry
    have h_left : Tendsto (fun a : ℝ => -(∫ t in a..1, Real.exp (-t) * Real.log t)) (𝓝[>] (0 : ℝ)) (𝓝 (-(∫ t in Set.Ioc 0 1, Real.exp (-t) * Real.log t))) := by
      have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.log t) (Set.Ioc 0 1) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.log t) (Set.Ioc 0 1) := by sorry
        refine' h_integrable.norm.mono' _ _
        · exact MeasureTheory.AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable (by continuity)) h_integrable.aestronglyMeasurable
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx using by rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _ |> le_of_lt)]; exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr <| by linarith [hx.1, hx.2])
      have h_set : Tendsto (fun a : ℝ => ∫ t in Set.Ioc a 1, Real.exp (-t) * Real.log t) (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in Set.Ioc 0 1, Real.exp (-t) * Real.log t)) := sorry
      refine' (h_set.congr' _).neg
      filter_upwards [self_mem_nhdsWithin] with a ha using by sorry
    have h_right₁ : Tendsto (fun a : ℝ => ∫ t in a..1, (1 - Real.exp (-t)) / t) (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t)) := by
      have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => (1 - Real.exp (-t)) / t) (Set.Ioc 0 1) := by
        sorry
      rw [intervalIntegral.integral_of_le zero_le_one]
      sorry
    have h_right₂ : Tendsto (fun a : ℝ => (1 - Real.exp (-a)) * Real.log a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h₁ : Tendsto (fun a : ℝ => (1 - Real.exp (-a)) / a) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        have hder : HasDerivAt (fun a : ℝ => 1 - Real.exp (-a)) 1 0 := by simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((hasDerivAt_neg (0 : ℝ)).exp)
        sorry--simpa [div_eq_mul_inv, sub_eq_add_neg] using hder.tendsto_slope_zero_right
      have h₂ : Tendsto (fun a : ℝ => a * Real.log a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
      sorry--simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h₁.mul h₂
    exact tendsto_nhds_unique h_left (by sorry)
  -- For the integral from 1 to ∞, integration by parts gives the required tail identity.
  have h_one_infty : ∫ t in Set.Ioi 1, Real.exp (-t) * Real.log t = ∫ t in Set.Ioi 1, Real.exp (-t) / t := by
    calc
      ∫ t in Set.Ioi 1, Real.exp (-t) * Real.log t = ∫ t in Set.Ioi 1, Real.log t * Real.exp (-t) := by refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => by ring
      _ = ∫ t in Set.Ioi 1, Real.exp (-t) / t := by
        sorry
  rw [h_gamma_deriv, h_split, neg_add, h_zero_one, h_one_infty]; ring

/-
PROBLEM
The Euler-Mascheroni constant equals ∫_0^1 (1-e^{-t})/t dt - ∫_1^∞ e^{-t}/t dt
PROVIDED SOLUTION
This follows from γ = -Γ'(1) and the fact that Γ'(1) = ∫_0^∞ e^{-t} log(t) dt.
Key steps:
1. γ = -Γ'(1) (from eulerMascheroniConstant_eq_neg_deriv)
2. Γ'(1) = ∫_0^∞ e^{-t} log(t) dt (this is the derivative of the Gamma integral ∫_0^∞ e^{-t} t^{s-1} dt at s=1)
3. -∫_0^∞ e^{-t} log(t) dt = ∫_0^1 (1-e^{-t})/t dt - ∫_1^∞ e^{-t}/t dt
Step 3 proof: Write log(t) as an integral.
For t ∈ (0,1): log(t) = -∫_t^1 1/s ds, so -e^{-t} log(t) = e^{-t} ∫_t^1 1/s ds
For t ∈ (1,∞): log(t) = ∫_1^t 1/s ds, so -e^{-t} log(t) = -e^{-t} ∫_1^t 1/s ds
By Fubini:
-∫_0^1 e^{-t} log(t) dt = ∫_0^1 e^{-t} (∫_t^1 1/s ds) dt = ∫_0^1 (1/s) (∫_0^s e^{-t} dt) ds = ∫_0^1 (1-e^{-s})/s ds
-∫_1^∞ e^{-t} log(t) dt = -∫_1^∞ e^{-t} (∫_1^t 1/s ds) dt = -∫_1^∞ (1/s)(∫_s^∞ e^{-t} dt) ds = -∫_1^∞ e^{-s}/s ds
Adding: γ = ∫_0^1 (1-e^{-s})/s ds - ∫_1^∞ e^{-s}/s ds
-/
-- set_option maxHeartbeats 1600000 in
lemma eulerMascheroni_eq_integral :
    eulerMascheroniConstant =
      (∫ t in (0:ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1:ℝ), exp (-t) / t := by
  -- Using the fact that $\gamma = -\Gamma'(1)$ and the integral representation of $\Gamma'(1)$, we can write
  have h_gamma_deriv : Real.eulerMascheroniConstant = -∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t := by
    have h_gamma_deriv : deriv Real.Gamma 1 = ∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t := by
      -- Option 1
      -- convert Complex.hasDerivAt_GammaIntegral (s := 1) (by simp)
      --   |>.congr_of_eventuallyEq ?_ |>.real_of_complex.deriv
      -- · simp [mul_comm, ← Complex.ofReal_mul, integral_complex_ofReal, - Complex.ofReal_exp]
      -- · have h_open : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt (by fun_prop) (by fun_prop)
      --   filter_upwards [h_open.mem_nhds (by simp)] with s hs using Complex.Gamma_eq_integral hs
      -- Option 2
      let I : ℂ := ∫ t : ℝ in Ioi 0, t ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t))
      have h_complex_gamma : HasDerivAt Complex.Gamma I (1 : ℂ) := by
        refine Complex.hasDerivAt_GammaIntegral (by simp) |>.congr_of_eventuallyEq ?_
        have h_open : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt (by fun_prop) (by fun_prop)
        filter_upwards [h_open.mem_nhds (by simp)] with s hs using (Complex.Gamma_eq_integral hs)
      convert h_complex_gamma.real_of_complex.deriv
      simp [I, mul_comm, ← Complex.ofReal_mul, integral_complex_ofReal, - Complex.ofReal_exp]
    rw [ ← h_gamma_deriv, Real.eulerMascheroniConstant_eq_neg_deriv ];
  -- We can split the integral into two parts: from 0 to 1 and from 1 to ∞.
  have h_split : ∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t = (∫ t in Set.Ioc 0 1, Real.exp (-t) * Real.log t) + (∫ t in Set.Ioi 1, Real.exp (-t) * Real.log t) := by
    -- rw [ ← MeasureTheory.setIntegral_union ]
    -- · simp
    -- · simp
    -- · simp
    -- · apply AEStronglyMeasurable.contin
    --   simp
    -- · apply GammaIntegral_convergent (show 0 < 1 by norm_num) |>.mono_set
    --   simp
    -- · simp
    rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
    · have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.log t) (Set.Ioc 0 1) := by
        rw [ ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one ];
        norm_num +zetaDelta at *;
      refine' h_integrable.norm.mono' _ _;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) ) h_integrable.aestronglyMeasurable;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ norm_mul, Real.norm_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.exp_le_one_iff.mpr <| by linarith [ hx.1, hx.2 ] ) ;
    · -- We'll use the fact that $\int_1^\infty e^{-t} \log t \, dt$ converges.
      have h_conv : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) * t) (Set.Ioi 1) := by
        have h_integrable : ∫ t in Set.Ioi 0, Real.exp (-t) * t = Real.Gamma 2 := by
          rw [ Real.Gamma_eq_integral ] <;> norm_num;
        exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity ) ) ( Set.Ioi_subset_Ioi zero_le_one );
      refine' h_conv.mono' _ _;
      · exact ContinuousOn.aestronglyMeasurable ( fun t ht => ContinuousAt.continuousWithinAt ( by exact ContinuousAt.mul ( ContinuousAt.rexp ( continuousAt_id.neg ) ) ( Real.continuousAt_log ( by linarith [ ht.out ] ) ) ) ) measurableSet_Ioi;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ Real.norm_eq_abs, abs_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( Real.log_nonneg ht.out.le ) ) ] ; exact mul_le_mul_of_nonneg_left ( le_trans ( Real.log_le_sub_one_of_pos ( zero_lt_one.trans ht.out ) ) ( by linarith ) ) ( Real.exp_pos _ |> le_of_lt ) ;
  -- For the integral from 0 to 1, we use the fact that $\log t = -\int_t^1 \frac{1}{s} ds$.
  have h_log_zero_one : ∫ t in Set.Ioc 0 1, Real.exp (-t) * Real.log t = -∫ t in Set.Ioc 0 1, ∫ s in t..1, Real.exp (-t) / s := by
    have h_log_zero_one : ∀ t ∈ Set.Ioc 0 1, Real.log t = -∫ s in t..1, 1 / s := by
      intro t ht; rw [ integral_one_div_of_pos ] <;> aesop;
    rw [ ← MeasureTheory.integral_neg ] ; exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ h_log_zero_one x hx ] ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hx.1.le ] ;
  -- By Fubini's theorem, we can interchange the order of integration.
  have h_fubini : ∫ t in Set.Ioc 0 1, ∫ s in t..1, Real.exp (-t) / s = ∫ s in Set.Ioc 0 1, ∫ t in Set.Ioc 0 s, Real.exp (-t) / s := by
    have h_fubini : ∫ t in Set.Ioc 0 1, ∫ s in t..1, Real.exp (-t) / s = ∫ t in Set.Ioc 0 1, ∫ s in Set.Ioc 0 1, (if t ≤ s then Real.exp (-t) / s else 0) := by
      refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => _;
      rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
      rw [ intervalIntegral.integral_of_le ht.2 ];
      rw [ ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
      grind;
    rw [ h_fubini, ← MeasureTheory.integral_integral_swap ];
    · norm_num [ ← MeasureTheory.integral_indicator, Set.indicator_apply ];
      grind +splitImp;
    · rw [ MeasureTheory.integrable_prod_iff ];
      · field_simp;
        constructor;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx;
          refine' MeasureTheory.Integrable.indicator _ _;
          · exact Continuous.integrableOn_Ioc ( by exact Continuous.div_const ( Real.continuous_exp.comp <| ContinuousNeg.continuous_neg ) _ );
          · exact measurableSet_Iic;
        · refine' MeasureTheory.Integrable.congr _ _;
          use fun x => ∫ y in Set.Ioc 0 x, Real.exp ( -y ) / x;
          · -- The integral of $\frac{e^{-y}}{x}$ over $(0, x)$ is $\frac{1 - e^{-x}}{x}$.
            have h_inner : ∀ x ∈ Set.Ioc 0 1, ∫ y in Set.Ioc 0 x, Real.exp (-y) / x = (1 - Real.exp (-x)) / x := by
              intro x hx; rw [ ← intervalIntegral.integral_of_le hx.1.le ] ; norm_num [ intervalIntegral.integral_comp_neg ] ;
            rw [ MeasureTheory.integrable_congr ( Filter.eventuallyEq_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun x hx => h_inner x hx ) ];
            refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => 1;
            · norm_num;
            · exact ContinuousOn.aestronglyMeasurable ( fun x hx => ContinuousAt.continuousWithinAt ( by exact ContinuousAt.div ( continuousAt_const.sub ( Real.continuous_exp.continuousAt.comp ( ContinuousAt.neg continuousAt_id ) ) ) continuousAt_id ( ne_of_gt hx.1 ) ) ) measurableSet_Ioc;
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by linarith [ hx.1, hx.2 ] ) hx.1.le ) ] ; exact div_le_one_of_le₀ ( by linarith [ hx.1, hx.2, Real.add_one_le_exp ( -x ) ] ) hx.1.le;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx;
            rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
            congr with y ; split_ifs <;> norm_num;
            · rw [ abs_of_nonneg ( div_nonneg ( Real.exp_nonneg _ ) hx.1.le ) ];
            · grind +revert;
            · grind;
            · aesop;
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.ite ( measurableSet_le measurable_snd measurable_fst ) ( by exact Measurable.div ( Real.continuous_exp.measurable.comp ( measurable_neg.comp measurable_snd ) ) measurable_fst ) measurable_const );
  -- For the integral from 1 to ∞, we use the fact that $\log t = \int_1^t \frac{1}{s} ds$.
  have h_log_one_infty : ∫ t in Set.Ioi 1, Real.exp (-t) * Real.log t = ∫ t in Set.Ioi 1, ∫ s in (1 : ℝ)..t, Real.exp (-t) / s := by
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => _;
    norm_num [ div_eq_mul_inv, ht.out.le ];
  -- By Fubini's theorem, we can interchange the order of integration for the integral from 1 to ∞.
  have h_fubini_one_infty : ∫ t in Set.Ioi 1, ∫ s in (1 : ℝ)..t, Real.exp (-t) / s = ∫ s in Set.Ioi 1, ∫ t in Set.Ioi s, Real.exp (-t) / s := by
    have h_fubini_one_infty : ∫ t in Set.Ioi 1, ∫ s in (1 : ℝ)..t, Real.exp (-t) / s = ∫ s in Set.Ioi 1, ∫ t in Set.Ioi 1, Real.exp (-t) / s * (if s ≤ t then 1 else 0) := by
      rw [ ← MeasureTheory.integral_integral_swap ];
      · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => _;
        rw [ intervalIntegral.integral_of_le ht.out.le, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        simpa only [ ← ite_and ];
      · rw [ MeasureTheory.integrable_prod_iff ];
        · constructor;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht;
            -- The function is integrable on $(1, t]$ and zero elsewhere, so it is integrable on $(1, \infty)$.
            have h_integrable : MeasureTheory.IntegrableOn (fun y => Real.exp (-t) / y) (Set.Ioc 1 t) := by
              exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const continuousAt_id <| by linarith [ hx.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
            rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_Ioc ) ] at h_integrable;
            rw [ MeasureTheory.integrable_congr ];
            convert h_integrable.restrict;
            filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with y hy using by rw [ Set.indicator_apply ] ; aesop;
          · refine' MeasureTheory.Integrable.congr _ _;
            use fun x => ∫ y in Set.Ioc 1 x, Real.exp ( -x ) / y;
            · -- The integral $\int_{1}^{x} \frac{e^{-x}}{y} \, dy$ simplifies to $e^{-x} \log x$.
              have h_inner : ∀ x ∈ Set.Ioi 1, ∫ y in Set.Ioc 1 x, Real.exp (-x) / y = Real.exp (-x) * Real.log x := by
                intro x hx; rw [ ← intervalIntegral.integral_of_le hx.out.le ] ; norm_num [ div_eq_mul_inv, hx.out.le ] ;
              rw [ MeasureTheory.integrable_congr ( Filter.eventuallyEq_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) h_inner ) ];
              have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * x) (Set.Ioi 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * x) (Set.Ioi 0) := by
                  have h_integrable : ∫ x in Set.Ioi 0, Real.exp (-x) * x = Real.Gamma 2 := by
                    rw [ Real.Gamma_eq_integral ] <;> norm_num;
                  exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity );
                exact h_integrable.mono_set <| Set.Ioi_subset_Ioi zero_le_one;
              refine' h_integrable.mono' _ _;
              · exact MeasureTheory.AEStronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) ) ( Real.measurable_log.aestronglyMeasurable );
              · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( Real.log_nonneg hx.out.le ) ) ] ; exact mul_le_mul_of_nonneg_left ( le_trans ( Real.log_le_sub_one_of_pos ( zero_lt_one.trans hx.out ) ) ( by linarith ) ) ( Real.exp_pos _ |> le_of_lt ) ;
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx;
              rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
              congr with y ; split_ifs <;> norm_num;
              · rw [ abs_of_nonneg ( div_nonneg ( Real.exp_nonneg _ ) ( by linarith ) ) ];
              · linarith;
              · grind +revert;
              · grind +qlia;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( by exact Measurable.mul ( Real.continuous_exp.measurable.comp ( measurable_neg.comp measurable_fst ) ) ( measurable_snd.inv ) ) ( by exact Measurable.ite ( measurableSet_le measurable_snd measurable_fst ) measurable_const measurable_const ) );
    rw [ h_fubini_one_infty ];
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s hs => _;
    rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ), ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ];
    simp +decide [ Set.indicator ];
    rw [ ← MeasureTheory.integral_congr_ae ];
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton s ) ] with x hx using by split_ifs <;> cases lt_or_gt_of_ne hx <;> linarith [ hs.out ] ;
  simp_all +decide [ div_eq_mul_inv, ← intervalIntegral.integral_of_le zero_le_one ];
  rw [ intervalIntegral.integral_of_le zero_le_one ] ; norm_num [ MeasureTheory.integral_mul_const, integral_exp_neg_Ioi ] ; ring_nf;
  norm_num [ integral_exp_Iic, ← intervalIntegral.integral_of_le zero_le_one ] ; ring_nf;
  rw [ intervalIntegral.integral_of_le zero_le_one ] ; rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ ← intervalIntegral.integral_of_le hx.1.le ] ] ; norm_num [ intervalIntegral.integral_comp_neg ] ; ring_nf;
  rw [ intervalIntegral.integral_of_le zero_le_one ]
/-
PROBLEM
For 0 < ε < min y 1, the PV integrand equals a sum of convergent pieces
PROVIDED SOLUTION
This is an algebraic identity. Steps:
1. Use integral_exp_div_neg_eq to rewrite the first integral: ∫_{-1/ε}^{-ε} exp(u)/u du = -∫_{ε}^{1/ε} exp(-t)/t dt
2. Use integral_exp_div_split to rewrite the second integral: ∫_{ε}^{y} exp(u)/u du = ∫_{ε}^{y} (exp(u)-1)/u du + log(y) - log(ε)
3. Split -∫_{ε}^{1/ε} exp(-t)/t dt = -∫_{ε}^{1} exp(-t)/t dt - ∫_{1}^{1/ε} exp(-t)/t dt (using intervalIntegral.integral_add_adjacent_intervals)
4. Note that -∫_{ε}^{1} exp(-t)/t dt - log(ε) = ∫_{ε}^{1} (1-exp(-t))/t dt since log(ε) = -∫_{ε}^{1} 1/t dt. More precisely: ∫_{ε}^{1} (1-exp(-t))/t dt = ∫_{ε}^{1} 1/t dt - ∫_{ε}^{1} exp(-t)/t dt = -log(ε) - ∫_{ε}^{1} exp(-t)/t dt.
5. Combining: -∫_{ε}^{1/ε} exp(-t)/t dt + ∫_{ε}^{y} (exp(u)-1)/u du + log(y) - log(ε)
   = -∫_{ε}^{1} exp(-t)/t dt - ∫_{1}^{1/ε} exp(-t)/t dt + ∫_{ε}^{y} (exp(u)-1)/u du + log(y) - log(ε)
   = ∫_{ε}^{1} (1-exp(-t))/t dt - ∫_{1}^{1/ε} exp(-t)/t dt + ∫_{ε}^{y} (exp(u)-1)/u du + log(y)
Use integral_exp_div_neg_eq, integral_exp_div_split, intervalIntegral.integral_add_adjacent_intervals, and algebraic manipulation.
-/
lemma pv_rewrite {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hε1 : ε < 1) (hεy : ε < y) :
    (∫ u in (-1/ε)..(-ε), exp u / u) + (∫ u in ε..y, exp u / u) =
    (∫ t in ε..1, (1 - exp (-t)) / t) - (∫ t in (1:ℝ)..(1/ε), exp (-t) / t) +
    (∫ u in ε..y, (exp u - 1) / u) + log y := by
  -- Use the results from the lemmas to rewrite the integrals.
  have h1 : ∫ u in (-1 / ε)..(-ε), Real.exp u / u = -(∫ t in ε..1 / ε, Real.exp (-t) / t) := by
    exact integral_exp_div_neg_eq hε
  have h2 : ∫ u in ε..y, Real.exp u / u = (∫ v in ε..y, ((Real.exp v) - 1) / v) + Real.log y - Real.log ε := by
    rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    rotate_right;
    use fun x => ∫ u in ε..x, ( Real.exp u - 1 ) / u + 1 / u;
    · rw [ intervalIntegral.integral_add ] <;> norm_num [ hε, hεy.le ];
      · rw [ Real.log_div ] <;> linarith;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div ( ContinuousAt.sub ( Real.continuous_exp.continuousAt ) continuousAt_const ) continuousAt_id ( by cases Set.mem_uIcc.mp hu <;> linarith );
      · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const continuousAt_id <| by linarith [ Set.mem_Icc.mp <| by simpa [ hε.le, hεy.le ] using hx ] ) ..;
    · intro x hx; convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
      use fun x => ∫ u in ε..x, Real.exp u / u;
      · apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div ( Real.continuous_exp.continuousAt ) continuousAt_id ( by cases Set.mem_uIcc.mp hu <;> cases Set.mem_uIcc.mp hx <;> linarith );
        · exact Measurable.stronglyMeasurable ( by exact Measurable.mul ( Real.continuous_exp.measurable ) ( measurable_id.inv ) ) |> fun h => h.stronglyMeasurableAtFilter;
        · exact ContinuousAt.div ( Real.continuous_exp.continuousAt ) continuousAt_id ( by cases Set.mem_uIcc.mp hx <;> linarith );
      · filter_upwards [ lt_mem_nhds ( show x > 0 by cases Set.mem_uIcc.mp hx <;> linarith ) ] with u hu using by refine' intervalIntegral.integral_congr fun v hv => _ ; rw [ sub_div, sub_add_cancel ] ;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div ( Real.continuous_exp.continuousAt ) continuousAt_id ( by cases Set.mem_uIcc.mp hu <;> linarith );
  rw [ h1, h2 ] ; ring_nf;
  rw [ intervalIntegral.integral_add ] <;> norm_num ; ring_nf;
  · rw [ integral_inv_of_pos, show ( ∫ u in ( ε : ℝ )..ε⁻¹, Real.exp ( -u ) * u⁻¹ ) = ( ∫ u in ( ε : ℝ )..1, Real.exp ( -u ) * u⁻¹ ) + ( ∫ u in ( 1 : ℝ )..ε⁻¹, Real.exp ( -u ) * u⁻¹ ) from ?_ ] <;> norm_num [ hε, hε1, hεy ] ; ring;
    rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ] <;> exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.mul ( ContinuousAt.rexp <| ContinuousAt.neg <| continuousAt_id ) <| ContinuousAt.inv₀ continuousAt_id <| by cases Set.mem_uIcc.mp hu <;> nlinarith [ inv_mul_cancel₀ hε.ne' ] ;
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.neg ( ContinuousAt.mul ( Real.continuous_exp.continuousAt.comp <| ContinuousAt.neg continuousAt_id ) <| ContinuousAt.inv₀ continuousAt_id <| by cases Set.mem_uIcc.mp ht <;> linarith );
  · exact Or.inr <| Set.notMem_uIcc_of_lt hε zero_lt_one
/-! ## Main theorem -/
theorem pv_exp_div_eq_gamma_add_log_add_integral {y : ℝ} (hy : 0 < y) :
    lim ((𝓝[>] (0 : ℝ)).map (fun ε =>
      (∫ u in (-1/ε)..(-ε), exp u / u) + ∫ u in ε..y, exp u / u)) =
    eulerMascheroniConstant + log y + ∫ u in (0 : ℝ)..y, ((exp u - 1) / u) := by
  -- Suffices to show Tendsto
  apply lim_eq
  -- Rewrite the target
  rw [show eulerMascheroniConstant + log y + ∫ u in (0 : ℝ)..y, ((exp u - 1) / u) =
    ((∫ t in (0:ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1:ℝ), exp (-t) / t) +
    (∫ u in (0:ℝ)..y, (exp u - 1) / u) + log y by
      rw [← eulerMascheroni_eq_integral]; ring]
  -- The rewritten form converges
  have h_rw : Tendsto
    (fun ε => (∫ t in ε..1, (1 - exp (-t)) / t) - (∫ t in (1:ℝ)..(1/ε), exp (-t) / t) +
      (∫ u in ε..y, (exp u - 1) / u) + log y)
    (𝓝[>] (0 : ℝ))
    (𝓝 (((∫ t in (0:ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1:ℝ), exp (-t) / t) +
      (∫ u in (0:ℝ)..y, (exp u - 1) / u) + log y)) := by
    exact ((tendsto_integral_one_sub_exp_neg_div.sub tendsto_integral_exp_neg_div_Ioi).add
      (tendsto_integral_exp_sub_one_div hy)).add tendsto_const_nhds
  -- Show the original function is eventually equal to the rewritten form
  apply h_rw.congr'
  have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < min y 1 := by
    apply nhdsWithin_le_nhds
    exact Iio_mem_nhds (lt_min hy one_pos)
  filter_upwards [this, self_mem_nhdsWithin] with ε hε hε_pos
  exact (pv_rewrite hy hε_pos (lt_of_lt_of_le hε (min_le_right _ _))
    (lt_of_lt_of_le hε (min_le_left _ _))).symm

#show_unused pv_exp_div_eq_gamma_add_log_add_integral
