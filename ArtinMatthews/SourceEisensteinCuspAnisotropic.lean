module

public import ArtinMatthews.SourceEisensteinFixedFiniteCusp
public import ArtinMatthews.SourceEisensteinNonconstantGradient
public import ArtinMatthews.SourceKPCuspDifferentialDescent
public import ArtinMatthews.SourceKPCuspNativeUpperTranslation
public import ArtinMatthews.SourceKPCuspAnisotropicHaar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual zero-mean Eisenstein remainder on each fixed cusp torus has
its proved anisotropic gap, with the native Cartesian derivatives identified. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Module Module.Free MeasureTheory Topology
open OAI.CubicEisenstein SourceHyperbolicGreen
open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice.Construction
open scoped NumberField MatrixGroups AdeleRing ContDiff Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (qf : SourceKPFiniteAdeleProjective K hζ)
local notation "E" => mixedEmbedding.mixedSpace K
local notation "P" => ProductSpace (InfinitePlace K)
local notation "D" => sourceKPFixedFiniteCuspPeriod K hζ qf
local notation "Q" => SourceKPCuspPrincipalQuotient K D
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "hd" => sourceKPFixedFiniteCuspPeriod_ne_zero K hζ qf
local instance sourceEisensteinCuspAnisotropicMeasurable : MeasurableSpace Q := borel Q
local instance sourceEisensteinCuspAnisotropicBorel : BorelSpace Q := ⟨rfl⟩

theorem sourceKPFixedFiniteCuspNonconstant_native_pullback
    (p : P) (hp : ∀ v, 0 < p v 2) (s : ℂ) (x : E) :
    sourceKPFixedFiniteCuspNonconstant K hζ qf s (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp)) (sourceKPCuspArchQuotientMap K D x) =
      sourceKPAdelicNonconstantProductChart K hζ s (1,qf) (sourceKPCuspNativePoint K hζ p x) := by
  change sourceKPFixedFiniteCuspNonconstant K hζ qf s (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp)) (QuotientAddGroup.mk (mixedAdelicAdd K x)) = _
  rw [sourceKPFixedFiniteCuspNonconstant_mk,sourceKPCuspNativeUpperLift_translate K hζ p hp x qf]
  have hpx (v : InfinitePlace K) : 0 < sourceKPCuspNativePoint K hζ p x v 2 := by
    rw [sourceKPCuspNativePoint_height]
    exact hp v
  rw [sourceKPAdelicNonconstantProductChart_apply_of_positive K hζ s (1,qf) _ hpx]
  apply congrArg (sourceKPAdelicNonconstantEisenstein K hζ s)
  exact Prod.ext (one_mul _).symm (mul_one _).symm

theorem sourceKPFixedFiniteCuspNonconstant_native_lift_C1
    (p : P) (hp : ∀ v, 0 < p v 2) {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    ContDiff ℝ 1 (fun x : E => sourceKPFixedFiniteCuspNonconstantContinuous K hζ qf hs (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp))
      (sourceKPCuspArchQuotientMap K D x)) := by
  have he : (fun x : E => sourceKPFixedFiniteCuspNonconstantContinuous K hζ qf hs (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp))
      (sourceKPCuspArchQuotientMap K D x)) =
      sourceKPAdelicNonconstantProductChart K hζ s (1,qf) ∘ sourceKPCuspNativePoint K hζ p :=
    funext (sourceKPFixedFiniteCuspNonconstant_native_pullback K hζ qf p hp s)
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hpx : sourceKPCuspNativePoint K hζ p x ∈ productUpper (InfinitePlace K) := by
    intro v _
    change 0 < sourceKPCuspNativePoint K hζ p x v 2
    rw [sourceKPCuspNativePoint_height]
    exact hp v
  exact (sourceKPAdelicNonconstantProductChart_contDiffAt K hζ hs (1,qf) _ hpx).comp x
    ((sourceKPCuspNativePoint_contDiff K hζ p).of_le (by simp)).contDiffAt

theorem sourceKPFixedFiniteCuspNonconstant_native_anisotropic
    (p : P) (hp : ∀ v, 0 < p v 2) {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1) :
    ∃ g : I → C(Q,ℂ),
      SourceKPCuspDirectionalDerivative K D hd
        (sourceKPFixedFiniteCuspNonconstantContinuous K hζ qf hs (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp))) g ∧
      (∀ (x : E) (v : InfinitePlace K) (k : Fin 2),
        sourceKPCuspPhysicalDerivativeC K D hζ hd g v k (sourceKPCuspArchQuotientMap K D x) =
          productPartial (sourceKPAdelicNonconstantProductChart K hζ s (1,qf)) v k.castSucc
            (sourceKPCuspNativePoint K hζ p x)) ∧
      sourceKPCuspHorizontalGapConstant K D * (∏ v, p v 2 ^ 2) ^
        (1 / (InfinitePlace.nrComplexPlaces K : ℝ)) *
        (∫ x, ‖sourceKPFixedFiniteCuspNonconstantContinuous K hζ qf hs (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp)) x‖ ^ 2
          ∂sourceKPCuspTraceHaar K D) ≤
        ∑ v, p v 2 ^ 2 * ∑ k : Fin 2,
          ∫ x, ‖sourceKPCuspPhysicalDerivativeC K D hζ hd g v k x‖ ^ 2 ∂sourceKPCuspTraceHaar K D := by
  letI := source_isTotallyComplex K hζ
  let f := sourceKPFixedFiniteCuspNonconstantContinuous K hζ qf hs (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp))
  let R := sourceKPAdelicNonconstantProductChart K hζ s (1,qf)
  have hF : ContDiff ℝ 1 (fun x : E => f (sourceKPCuspArchQuotientMap K D x)) :=
    sourceKPFixedFiniteCuspNonconstant_native_lift_C1 K hζ qf p hp hs
  obtain ⟨g,hfg,_⟩ := sourceKPCusp_directionalDerivative_of_C1_lift K D hd f hF
  refine ⟨g,hfg,?_,?_⟩
  · intro x v k
    let e := sourceKPCuspPhysicalDirection K hζ v k
    have he : sourceKPCuspProductHorizontalCLM K e = productDirection v k.castSucc :=
      sourceKPCuspProductHorizontalCLM_direction K v k
    have ha : (fun t : ℝ => sourceKPCuspNativePoint K hζ p (x+t•e)) =
        fun t => sourceKPCuspNativePoint K hζ p x+t•productDirection v k.castSucc := by
      funext t
      change p + sourceKPCuspProductHorizontalCLM K (x+t•e) =
        (p + sourceKPCuspProductHorizontalCLM K x)+t•productDirection v k.castSucc
      rw [map_add,map_smul,he,add_assoc]
    have hl : HasDerivAt (fun t : ℝ => sourceKPCuspNativePoint K hζ p (x+t•e))
        (productDirection v k.castSucc) 0 := by
      rw [ha]
      simpa only [id_eq,one_smul] using
        (((hasDerivAt_id (0 : ℝ)).smul_const (productDirection v k.castSucc)).const_add
          (sourceKPCuspNativePoint K hζ p x))
    have hx : sourceKPCuspNativePoint K hζ p x ∈ productUpper (InfinitePlace K) := by
      intro w _
      change 0 < sourceKPCuspNativePoint K hζ p x w 2
      rw [sourceKPCuspNativePoint_height]
      exact hp w
    have hn := ((sourceKPAdelicNonconstantProductChart_contDiffAt K hζ hs (1,qf) _ hx).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp only [zero_smul,add_zero])
    have hf := sourceKPCuspPhysicalDerivativeC_hasDerivAt K D hζ hd f g hfg
      (hF.differentiable (by norm_num)) v k x 0
    have hpull (z : E) : f (sourceKPCuspArchQuotientMap K D z) = R (sourceKPCuspNativePoint K hζ p z) :=
      sourceKPFixedFiniteCuspNonconstant_native_pullback K hζ qf p hp s z
    simp only [hpull,zero_smul,add_zero] at hf
    exact hf.unique (by simpa only [Function.comp_def,productPartial] using hn)
  · exact sourceKPCusp_directional_anisotropic_poincare K D hζ hd f g hfg
      (sourceKPFixedFiniteCuspNonconstant_mean_zero K hζ qf hs (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp))) (fun v => p v 2) hp

end
end ArtinMatthews
