module

public import ArtinMatthews.SourceKPHighCuspQuotient
public import ArtinMatthews.SourceKPCuspLevelTopology
public import ArtinMatthews.SourceKPAdelicCuspBand


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical adelic upper root acts continuously on the actual finite
level and preserves its literal high representative set. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCuspFiniteUpper_eventually_fixed
    (b : SourceKPFiniteLevelFiber K hζ) :
    ∀ᶠ t : 𝔸ᶠ[K] in 𝓝 0, sourceKPFiniteAdeleUpperLift K hζ t • b = b := by
  obtain ⟨qf,rfl⟩ := Quotient.mk_surjective b
  let q : SourceKPAdelicProjective K hζ := (1,qf)
  filter_upwards [sourceKPAdelicFiniteConjugate_eventually_compact K hζ q] with t ht
  let n := sourceKPAdelicUpperLift K hζ (0,t)
  have hn : n.1 = 1 := by
    change ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) 0) = 1
    rw [sourceKPUpperMatrix_zero, map_one]
  have harch : (q⁻¹*n*q).1 = 1 := by
    change q.1⁻¹*n.1*q.1 = 1
    rw [hn, mul_one, inv_mul_cancel]
  obtain ⟨k,hk⟩ := sourceKPAdelicDeepCompact_finite_lift K hζ _ ht harch
  change q⁻¹ * n * q = sourceKPFiniteDeepCoverLift K hζ k at hk
  have heq : q * sourceKPFiniteDeepCoverLift K hζ k = n*q := by
    rw [← hk, ← mul_assoc, mul_inv_cancel_left]
  have hf := (sourceKPFiniteLevelMk_eq_iff K hζ q (n*q)).2 ⟨k,heq⟩
  exact (congrArg Prod.snd hf).symm

theorem sourceKPCuspFiniteUpper_continuous (b : SourceKPFiniteLevelFiber K hζ) :
    Continuous (fun t : 𝔸ᶠ[K] => sourceKPFiniteAdeleUpperLift K hζ t • b) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hsub : Continuous (fun u : 𝔸ᶠ[K] => u-t) := continuous_id.sub continuous_const
  have ht : Tendsto (fun u : 𝔸ᶠ[K] => u-t) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self] using hsub.tendsto t
  have he : (fun u : 𝔸ᶠ[K] => sourceKPFiniteAdeleUpperLift K hζ u • b) =ᶠ[𝓝 t]
      fun _ => sourceKPFiniteAdeleUpperLift K hζ t • b := by
    filter_upwards [ht.eventually (sourceKPCuspFiniteUpper_eventually_fixed K hζ b)] with u hu
    calc
      _ = sourceKPFiniteAdeleUpperLift K hζ (t+(u-t)) • b := by
        rw [show t+(u-t)=u by abel]
      _ = _ := by rw [sourceKPFiniteAdeleUpperLift_add, mul_smul, hu]
  have hc : ContinuousAt (fun _ : 𝔸ᶠ[K] => sourceKPFiniteAdeleUpperLift K hζ t • b) t :=
    continuousAt_const
  exact hc.congr_of_eventuallyEq he

theorem sourceKPCuspUpperAction_continuous :
    Continuous (fun p : 𝔸[K] × SourceKPFiniteLevelSpace K hζ =>
      sourceKPAdelicUpperLift K hζ p.1 • p.2) := by
  have hf : Continuous (fun p : 𝔸ᶠ[K] × SourceKPFiniteLevelFiber K hζ =>
      sourceKPFiniteAdeleUpperLift K hζ p.1 • p.2) :=
    continuous_prod_of_discrete_right.mpr (sourceKPCuspFiniteUpper_continuous K hζ)
  have ha : Continuous (fun y : InfiniteAdeleRing K =>
      ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) y)) :=
    QuotientGroup.continuous_mk.comp (sourceKPCuspUpperArch_continuous K)
  let X := 𝔸[K] × SourceKPFiniteLevelSpace K hζ
  have h₁ : Continuous (fun p : X => p.1.1) := continuous_fst.comp continuous_fst
  have h₂ : Continuous (fun p : X => p.2.1) := continuous_fst.comp continuous_snd
  have h₃ : Continuous (fun p : X => p.1.2) := continuous_snd.comp continuous_fst
  have h₄ : Continuous (fun p : X => p.2.2) := continuous_snd.comp continuous_snd
  have h₅ : Continuous (fun p : X => (p.1.2,p.2.2)) := h₃.prodMk h₄
  have hArch : Continuous (fun p : X =>
      ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) p.1.1) * p.2.1) :=
    (ha.comp h₁).mul h₂
  have hFin := Continuous.comp' (f := fun p : X => (p.1.2,p.2.2))
    (g := fun p : 𝔸ᶠ[K] × SourceKPFiniteLevelFiber K hζ =>
      sourceKPFiniteAdeleUpperLift K hζ p.1 • p.2) hf h₅
  exact hArch.prodMk hFin

theorem sourceKPFiniteLevelHeight_left_upper (y : 𝔸[K])
    (x : SourceKPFiniteLevelSpace K hζ) :
    sourceKPFiniteLevelHeight K hζ (sourceKPAdelicUpperLift K hζ y • x) =
      sourceKPFiniteLevelHeight K hζ x := by
  obtain ⟨q,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
  let n := sourceKPAdelicUpperLift K hζ y
  let H := sourceKPFiniteLevelHeight K hζ
  calc
    H (n • sourceKPFiniteLevelMk K hζ q) = H (sourceKPFiniteLevelMk K hζ (n*q)) :=
      congrArg H (sourceKPFiniteLevelMk_mul K hζ n q).symm
    _ = sourceKPAdelicCoverHeight K hζ (n*q) := sourceKPFiniteLevelHeight_mk K hζ (n*q)
    _ = sourceKPAdelicCoverHeight K hζ q := sourceKPAdelicCoverHeight_left_upper K hζ y q
    _ = H (sourceKPFiniteLevelMk K hζ q) := (sourceKPFiniteLevelHeight_mk K hζ q).symm

@[instance_reducible]
private def sourceKPCuspRestrictAction {G X : Type*} [Monoid G] [MulAction G X]
    (P : X → Prop) (h : ∀ (g : G) (x : X), P x → P (g • x)) : MulAction G (Subtype P) where
  smul g x := ⟨g • x.val, h g x.val x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance sourceKPCuspHighUpperMulAction (T : ℝ) :
    MulAction (Multiplicative 𝔸[K]) (SourceKPHighCuspFinite K hζ T) := by
  let : MulAction (Multiplicative 𝔸[K]) (SourceKPFiniteLevelSpace K hζ) :=
    MulAction.compHom _ (sourceKPAdelicUpperHom K hζ)
  exact sourceKPCuspRestrictAction (fun x => T < sourceKPFiniteLevelHeight K hζ x)
    (fun y x hx => (sourceKPFiniteLevelHeight_left_upper K hζ y.toAdd x).symm ▸ hx)

theorem sourceKPCuspHighUpper_val (T : ℝ) (y : 𝔸[K]) (x : SourceKPHighCuspFinite K hζ T) :
    (Multiplicative.ofAdd y • x).val = sourceKPAdelicUpperLift K hζ y • x.val := rfl

theorem sourceKPCuspHighUpperAction_continuous (T : ℝ) :
    Continuous (fun p : 𝔸[K] × SourceKPHighCuspFinite K hζ T =>
      Multiplicative.ofAdd p.1 • p.2) := by
  apply continuous_induced_rng.mpr
  have hf : Continuous (fun p : 𝔸[K] × SourceKPHighCuspFinite K hζ T => (p.1,p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hc := (sourceKPCuspUpperAction_continuous K hζ).comp hf
  simpa only [Function.comp_def, sourceKPCuspHighUpper_val] using hc

theorem sourceKPCuspHighUpper_height (T : ℝ) (y : 𝔸[K])
    (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPFiniteLevelHeight K hζ (Multiplicative.ofAdd y • x).val =
      sourceKPFiniteLevelHeight K hζ x.val := by
  rw [sourceKPCuspHighUpper_val]
  exact sourceKPFiniteLevelHeight_left_upper K hζ y x.val

end
end ArtinMatthews
