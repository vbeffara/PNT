import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators Set

attribute [fun_prop] Integrable Integrable.norm Integrable.const_mul Integrable.add Integrable.sub
attribute [fun_prop] AEStronglyMeasurable Continuous.aestronglyMeasurable
attribute [fun_prop] HasCompactSupport HasCompactSupport.smul_right HasCompactSupport.smul_right HasCompactSupport.mul_left

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

def CD (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : AddSubgroup (ℝ → E) where
  carrier := {f | ContDiff ℝ n f}
  zero_mem' := by change ContDiff ℝ (↑n) (fun _ => 0) ; apply contDiff_const
  add_mem' hf hg := hf.add hg
  neg_mem' hf := by simp at hf ⊢ ; exact hf.neg

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ⊤ ofReal' := by
  have key x : HasDerivAt ofReal' 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal' = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_top_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

@[fun_prop] nonrec lemma HasCompactSupport.iteratedDeriv {f : ℝ → E} (hf : HasCompactSupport f) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa [iteratedDeriv_succ] using ih.deriv

end lemmas

namespace CD

variable {f : CD n E} {R x v : ℝ}

instance : CoeFun (CD n E) (fun _ => ℝ → E) where coe f := f.1

instance : Coe (CD n ℝ) (CD n ℂ) where coe f := ⟨ofReal' ∘ f, contDiff_ofReal.of_le le_top |>.comp f.2⟩

def of_le (f : CD n E) {m : ℕ} (hm : m ≤ n) : CD m E := ⟨f, f.2.of_le (by simp [hm])⟩

def of_succ (f : CD (n + 1) E) : CD n E := ⟨f, f.2.of_succ⟩

instance : Coe (CD (n + 1) E) (CD n E) where coe f := of_succ f

def const_smul (R : ℝ) (f : CD n E) : CD n E := ⟨R • f, f.2.const_smul R⟩

instance : HSMul ℝ (CD n E) (CD n E) where hSMul := const_smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

@[continuity, fun_prop] lemma continuous (f : CD n E) : Continuous f := f.2.continuous

noncomputable nonrec def deriv (f : CD (n + 1) E) : CD n E := ⟨deriv f, (contDiff_succ_iff_deriv.mp f.2).2⟩

lemma hasDerivAt (f : CD (n + 1) E) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  (f.2.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_apply {f : CD (n + 1) E} {x : ℝ} : deriv f x = _root_.deriv f x := rfl

lemma deriv_const_smul {f : CD (n + 1) E} : deriv (R • f) = R • deriv f := by
  ext x ; exact (hasDerivAt f x |>.const_smul R).deriv

noncomputable def scale (g : CD n E) (R : ℝ) : CD n E := by
  by_cases R = 0
  · exact ⟨0, contDiff_const⟩
  · exact ⟨funscale g R, g.2.comp (contDiff_const.smul contDiff_id)⟩

lemma deriv_scale {f : CD (n + 1) E} : deriv (scale f R) = R⁻¹ • scale (deriv f) R := by
  ext v ; by_cases hR : R = 0 <;> simp [hR, scale]
  · simp [deriv, const_smul] ; exact deriv_const _ _
  · exact ((hasDerivAt f (R⁻¹ • v)).scomp v (by simpa using (hasDerivAt_id v).const_smul R⁻¹)).deriv

@[simp] lemma deriv_scale' {f : CD (n + 1) E} : deriv (scale f R) v = R⁻¹ • deriv f (R⁻¹ • v) := by
  rw [deriv_scale] ; by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CD (n + 1) E) (R x : ℝ) :
    HasDerivAt (scale f R) (R⁻¹ • deriv f (R⁻¹ • x)) x := by
  simpa using hasDerivAt (scale f R) x

lemma tendsto_scale (f : CD n E) (x : ℝ) : Tendsto (fun R => scale f R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.2.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

def mul (f g : CD n 𝕜) : CD n 𝕜 := ⟨f * g, f.2.mul g.2⟩

instance : Mul (CD n 𝕜) where mul := mul

nonrec lemma deriv_mul (f g : CD (n + 1) 𝕜) : deriv (f * g) = deriv f * of_succ g + of_succ f * deriv g := by
  ext t
  have l1 : DifferentiableAt ℝ f t := (f.2.differentiable (by simp)).differentiableAt
  have l2 : DifferentiableAt ℝ g t := (g.2.differentiable (by simp)).differentiableAt
  exact deriv_mul l1 l2

def smul (f : CD n ℝ) (g : CD n E) : CD n E := ⟨fun t => f t • g t, f.2.smul g.2⟩

instance : SMul (CD n ℝ) (CD n E) where smul := smul

nonrec lemma deriv_smul (f : CD (n + 1) ℝ) (g : CD (n + 1) E) :
    deriv (f • g) = of_succ f • deriv g + deriv f • of_succ g := by
  ext t
  have l1 : DifferentiableAt ℝ f t := (f.2.differentiable (by simp)).differentiableAt
  have l2 : DifferentiableAt ℝ g t := (g.2.differentiable (by simp)).differentiableAt
  exact deriv_smul l1 l2

noncomputable nonrec def iteratedDeriv (k : ℕ) (f : CD (n + k) E) : CD n E := by
  refine ⟨iteratedDeriv k f, ?_⟩
  simpa [iteratedDeriv_eq_iterate] using f.2.iterate_deriv' n k

noncomputable def iteratedDeriv_of_le {n : ℕ} ⦃k : ℕ⦄ (hk : k ≤ n) (f : CD n E) : CD (n - k) E := by
  refine ⟨_root_.iteratedDeriv k f, ?_⟩
  have := Nat.le.dest hk ; simp_rw [add_comm k] at this ; obtain ⟨l, rfl⟩ := this ; simp
  simpa [iteratedDeriv_eq_iterate] using f.2.iterate_deriv' l k

@[simp] lemma iteratedDeriv_of_le_zero (hk : k ≤ n) : iteratedDeriv_of_le hk (0 : CD n E) = 0 := sorry

@[simp] lemma iteratedDeriv_of_le_add (hk : k ≤ n) (f g : CD n E) :
    iteratedDeriv_of_le hk (f + g) = iteratedDeriv_of_le hk f + iteratedDeriv_of_le hk g := sorry

@[simp] lemma iteratedDeriv_of_le_neg (hk : k ≤ n) (f : CD n E) :
    iteratedDeriv_of_le hk (-f) = -iteratedDeriv_of_le hk f := sorry

nonrec lemma iteratedDeriv_succ {k : ℕ} {f : CD (n + (k + 1)) E} :
    iteratedDeriv (k + 1) f = iteratedDeriv k (deriv f) := by
  simp [iteratedDeriv, iteratedDeriv_succ'] ; rfl

nonrec lemma deriv_add (f g : CD (n + 1) E) : deriv (f + g) = deriv f + deriv g := by
  ext x
  apply deriv_add
  · exact (f.2.differentiable (by simp)).differentiableAt
  · exact (g.2.differentiable (by simp)).differentiableAt

lemma iteratedDeriv_add {k : ℕ} {f g : CD (n + k) E} :
    iteratedDeriv k (f + g) = iteratedDeriv k f + iteratedDeriv k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp_rw [iteratedDeriv_succ, deriv_add, ih]

lemma iteratedDeriv_add' {k : ℕ} {f g : CD (n + k) E} {x : ℝ} :
    iteratedDeriv k (f + g) x = iteratedDeriv k f x + iteratedDeriv k g x := by
  rw [iteratedDeriv_add] ; rfl

end CD

def CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : AddSubgroup (CD n E) where
  carrier := {f | HasCompactSupport f}
  zero_mem' := by change HasCompactSupport (fun _ => 0) ; simp [HasCompactSupport, tsupport]
  add_mem' hf hg := hf.add hg
  neg_mem' hf := by simpa [HasCompactSupport, tsupport] using hf

namespace CS

variable {f : CS n E} {R x v : ℝ}

-- lemma ext_CD {f g : CS n E} (h : f.toCD = g.toCD) : f = g := by
--   cases f ; cases g ; simp ; exact h

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe f := f.1

instance : Coe (CS n E) (CD n E) where coe f := f.1

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨f, f.2.comp_left (g := ofReal') rfl⟩

nonrec def of_le (f : CS n E) {m : ℕ} (hm : m ≤ n) : CS m E := ⟨CD.of_le f hm, by exact f.2⟩

nonrec def of_succ (f : CS (n + 1) E) : CS n E := of_le f (by simp)

instance : Coe (CS (n + 1) E) (CS n E) where coe := of_succ

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

noncomputable nonrec def deriv (f : CS (n + 1) E) : CS n E := ⟨CD.deriv f, f.2.deriv⟩

nonrec lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (deriv f x) x := CD.hasDerivAt _ _

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : deriv f x = _root_.deriv f x := rfl

lemma deriv_smul {f : CS (n + 1) E} : deriv (R • f) = R • deriv f := by
  ext x ; exact (hasDerivAt f x |>.const_smul R).deriv

noncomputable nonrec def scale (g : CS n E) (R : ℝ) : CS n E := by
  refine ⟨CD.scale g R, ?_⟩
  by_cases h : R = 0 <;> simp [CD.scale, h]
  · simp [CS, HasCompactSupport, tsupport]
  · exact g.2.comp_smul (inv_ne_zero h)

nonrec lemma deriv_scale {f : CS (n + 1) E} : deriv (scale f R) = R⁻¹ • scale (deriv f) R := by
  ext1 ; exact CD.deriv_scale

nonrec lemma of_succ_scale {f : CS (n + 1) E} : scale (of_succ f) R = of_succ (scale f R) := by
  ext ; by_cases hR : R = 0 <;> simp [scale, CD.scale, of_succ, of_le, CD.of_le, hR]

@[simp] lemma deriv_scale' {f : CS (n + 1) E} : deriv (scale f R) v = R⁻¹ • deriv f (R⁻¹ • v) := CD.deriv_scale'

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (scale f R) (R⁻¹ • deriv f (R⁻¹ • x)) x := CD.hasDerivAt_scale _ _ _

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => scale f R x) atTop (𝓝 (f 0)) := CD.tendsto_scale _ _

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ := (continuous_norm.comp f.1.2.continuous).exists_forall_ge_of_hasCompactSupport f.2.norm
  refine ⟨_, hx⟩

@[simp] lemma bounded' : BddAbove (range fun v ↦ ‖f v‖) :=
  (f.2.norm.isCompact_range (by fun_prop)).bddAbove

lemma bounded'_of_le (hk : k ≤ n) : BddAbove (range fun v ↦ ‖iteratedDeriv k f v‖) := by
  apply IsCompact.bddAbove
  apply f.2.iteratedDeriv.norm.isCompact_range
  exact f.1.2.continuous_iteratedDeriv k (by simp [hk]) |>.norm

lemma integrable (f : CS n E) : Integrable f := f.1.2.continuous.integrable_of_hasCompactSupport f.2

lemma integrable_iteratedDeriv {n : ℕ} (f : CS n E) : Integrable (iteratedDeriv n f) := by
  induction n with
  | zero => exact integrable f
  | succ n ih => simpa [iteratedDeriv_succ'] using ih (deriv f)

lemma integrable_iteratedDeriv_of_le {n : ℕ} (f : CS n E) ⦃k : ℕ⦄ (hk : k ≤ n) : Integrable (iteratedDeriv k f) := by
  obtain ⟨m, rfl⟩ := Nat.le.dest hk ; exact integrable_iteratedDeriv (of_le f hk)

noncomputable def norm (f : CS n E) : ℝ :=
  Finset.sup' (s := Finset.range (n + 1)) (by simp) (fun k => ⨆ v, ‖iteratedDeriv k f v‖)

noncomputable instance : Norm (CS n E) where norm := norm

@[simp] nonrec lemma norm_nonneg : 0 ≤ ‖f‖ := by
  simp [Norm.norm, norm] ; use 0 ; simp
  apply (norm_nonneg (f 0)).trans
  apply le_ciSup (f := fun x => ‖f x‖) bounded'

lemma le_norm (f : CS n E) (x : ℝ) : ‖f x‖ ≤ ‖f‖ := by
  apply (le_ciSup bounded' x).trans
  exact Finset.le_sup' (b := 0) (fun k => ⨆ v, ‖iteratedDeriv k f v‖) (by simp)

lemma le_norm_of_le (f : CS n E) (hk : k ≤ n) (x : ℝ) : ‖iteratedDeriv k f x‖ ≤ ‖f‖ := by
  apply (le_ciSup (bounded'_of_le hk) x).trans
  refine Finset.le_sup' (b := k) (fun k => ⨆ v, ‖iteratedDeriv k f v‖) (by simp ; omega)

lemma norm_of_succ (f : CS (n + 1) E) : ‖of_succ f‖ ≤ ‖f‖ := by
  simp_rw [Norm.norm, norm] ; apply Finset.sup'_mono ; simp

lemma norm_succ {f : CS (n + 1) E} : ‖f‖ = (⨆ v, ‖f v‖) ⊔ ‖deriv f‖ := by
  simp_rw [Norm.norm, norm, deriv, CD.deriv, ← iteratedDeriv_succ']
  let s : ℕ ↪ ℕ := ⟨fun n => n + 1, Nat.succ_injective⟩
  have l1 : _ = Finset.sup' (.range (n + 1)) _ ((fun k ↦ ⨆ v, ‖iteratedDeriv (k + 1) f v‖)) :=
    @Finset.sup'_map ℝ ℕ ℕ _ (.range (n + 1)) s (fun k => ⨆ v, ‖iteratedDeriv k f v‖) (by simp)
  have l2 : Finset.map s (Finset.range (n + 1)) = Finset.Ico 1 (n + 2) := by
    ext i ; simp [s] ; constructor
    · rintro ⟨a, h1, h2⟩ ; omega
    · rintro ⟨h1, h2⟩ ; use i - 1 ; omega
  have l3 : insert 0 (Finset.Ico 1 (n + 2)) = Finset.range (n + 2) := by ext i ; simp ; omega
  simp [← l1, l2, ← l3]

lemma norm_deriv (f : CS (n + 1) E) : ‖deriv f‖ ≤ ‖f‖ := by simp [norm_succ]

lemma norm_smul (c : ℝ) (f : CS n E) : ‖c • f‖ = |c| * ‖f‖ := by sorry

lemma norm_scale (R : ℝ) (hR : R ≠ 0) (f : CS n E) : ‖scale f R‖ = ‖f‖ := sorry

end CS

structure trunc where
  toFun : CS 2 ℝ
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ ⇑toFun
  h4 : ⇑toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := toFun

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 := (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

def W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : AddSubgroup (CD n E) where
  carrier := {f | ∀ ⦃k : ℕ⦄ (hk : k ≤ n), Integrable (CD.iteratedDeriv_of_le hk f)}
  zero_mem' k hk := by simp ; exact integrable_zero ℝ E _
  add_mem' {f g} hf hg k hk := by simpa using (hf hk).add (hg hk)
  neg_mem' {f} hf := by simpa using hf
