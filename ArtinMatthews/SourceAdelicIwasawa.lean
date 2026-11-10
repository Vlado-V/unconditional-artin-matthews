module

public import ArtinMatthews.SourceArchIwasawaCompletion
public import ArtinMatthews.SourceAdelicIwasawaAssembly
public import ArtinMatthews.SourceFiniteIwasawaHeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The base adelic Iwasawa decomposition, with genuine adelic factors. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPGL2ProductEquiv : GL (Fin 2) 𝔸[K] ≃*
    GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) 𝔸ᶠ[K] :=
  MulEquiv.ofBijective (sourceKPGL2ProductMap (InfiniteAdeleRing K) 𝔸ᶠ[K])
    ⟨sourceKPGL2ProductMap_injective _ _, sourceKPGL2ProductMap_surjective _ _⟩

def sourceKPAdelicBaseFiniteAt (P : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) 𝔸[K] →* GL (Fin 2) (P.adicCompletion K) :=
  (sourceKPAdeleMatrixAt K P).comp
    ((MonoidHom.snd _ _).comp (sourceKPGL2ProductEquiv K).toMonoidHom)

def sourceKPAdelicBaseComplexAt (v : InfinitePlace K) : GL (Fin 2) 𝔸[K] →* GL (Fin 2) ℂ :=
  (sourceKPArchMatrixComplexEquiv K hζ v).toMonoidHom.comp
    ((Pi.evalMonoidHom (fun w : InfinitePlace K => GL (Fin 2) w.Completion) v).comp
      ((sourceArchGLPiEquiv K).toMonoidHom.comp
        ((MonoidHom.fst _ _).comp (sourceKPGL2ProductEquiv K).toMonoidHom)))

def SourceKPAdelicBaseCompactMatrix : Subgroup (GL (Fin 2) 𝔸[K]) where
  carrier := {g | (∀ P, SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdelicBaseFiniteAt K P g)) ∧
    ∀ v, sourceKPAdelicBaseComplexAt K hζ v g ∈ sourceArchUnitaryGL.range}
  one_mem' := by
    constructor
    · intro P
      rw [map_one]
      exact sourceKPIntegralMatrix_one _
    · intro v
      rw [map_one]
      exact sourceArchUnitaryGL.range.one_mem
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    constructor
    · intro P
      rw [map_mul]
      exact sourceKPIntegralMatrix_mul _ (hg P) (hh P)
    · intro v
      rw [map_mul]
      exact sourceArchUnitaryGL.range.mul_mem (hg' v) (hh' v)
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    constructor
    · intro P
      rw [map_inv]
      exact sourceKPIntegralMatrix_inv _ (hg P)
    · intro v
      rw [map_inv]
      exact sourceArchUnitaryGL.range.inv_mem (hg' v)

def sourceKPAdelicBaseCompact : Subgroup PGL(2, 𝔸[K]) :=
  (SourceKPAdelicBaseCompactMatrix K hζ).map ProjGenLinGroup.mk

def sourceKPAdelicIwasawaBorel (g : GL (Fin 2) 𝔸[K]) : GL (Fin 2) 𝔸[K] :=
  (sourceKPGL2ProductEquiv K).symm
    (sourceKPArchIwasawaBorel K hζ (sourceKPGL2ProductEquiv K g).1,
      sourceKPAdeleIwasawaBorel K (sourceKPGL2ProductEquiv K g).2)

def sourceKPAdelicIwasawaCompact (g : GL (Fin 2) 𝔸[K]) : GL (Fin 2) 𝔸[K] :=
  (sourceKPGL2ProductEquiv K).symm
    (sourceKPArchIwasawaCompact K hζ (sourceKPGL2ProductEquiv K g).1,
      sourceKPAdeleIwasawaIntegral K (sourceKPGL2ProductEquiv K g).2)

def sourceKPAdelicIwasawaScalar (g : GL (Fin 2) 𝔸[K]) : 𝔸[K]ˣ :=
  sourceKPUnitPair (sourceKPArchIwasawaScalar K hζ (sourceKPGL2ProductEquiv K g).1)
    (sourceKPAdeleIwasawaScalar K (sourceKPGL2ProductEquiv K g).2)

theorem sourceKPAdelicIwasawaScalar_arch (g : GL (Fin 2) 𝔸[K]) :
    Units.map (RingHom.fst (InfiniteAdeleRing K) 𝔸ᶠ[K]).toMonoidHom (sourceKPAdelicIwasawaScalar K hζ g) =
      sourceKPArchIwasawaScalar K hζ (sourceKPGL2ProductEquiv K g).1 := by
  apply Units.ext
  rfl

theorem sourceKPAdelicIwasawaScalar_finite (g : GL (Fin 2) 𝔸[K]) :
    Units.map (RingHom.snd (InfiniteAdeleRing K) 𝔸ᶠ[K]).toMonoidHom (sourceKPAdelicIwasawaScalar K hζ g) =
      sourceKPAdeleIwasawaScalar K (sourceKPGL2ProductEquiv K g).2 := by
  apply Units.ext
  rfl

theorem sourceKPAdelicIwasawaScalar_at (g : GL (Fin 2) 𝔸[K])
    (P : HeightOneSpectrum (𝓞 K)) :
    Units.map (sourceKPAdeleEval K P).toMonoidHom
      (Units.map (RingHom.snd (InfiniteAdeleRing K) 𝔸ᶠ[K]).toMonoidHom (sourceKPAdelicIwasawaScalar K hζ g)) =
        (sourceKPLocalIwasawa K P (sourceKPAdelicBaseFiniteAt K P g)).scalar := by
  rw [sourceKPAdelicIwasawaScalar_finite]
  exact sourceKPAdeleIwasawaScalar_at K (sourceKPGL2ProductEquiv K g).2 P

theorem sourceKPAdelicIwasawaBorel_mem (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicIwasawaBorel K hζ g ∈ sourceKPRingNormalizedBorel 𝔸[K] := by
  have h := (sourceKPGL2ProductEquiv K).apply_symm_apply
    (sourceKPArchIwasawaBorel K hζ (sourceKPGL2ProductEquiv K g).1,
      sourceKPAdeleIwasawaBorel K (sourceKPGL2ProductEquiv K g).2)
  constructor
  · apply Prod.ext
    · exact (congrArg (fun a => a.1 1 0) h).trans (sourceKPArchIwasawaBorel_mem K hζ _).1
    · exact (congrArg (fun a => a.2 1 0) h).trans (sourceKPAdeleIwasawaBorel_mem K _).1
  · apply Prod.ext
    · exact (congrArg (fun a => a.1 1 1) h).trans (sourceKPArchIwasawaBorel_mem K hζ _).2
    · exact (congrArg (fun a => a.2 1 1) h).trans (sourceKPAdeleIwasawaBorel_mem K _).2

theorem sourceKPAdelicIwasawaCompact_mem (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicIwasawaCompact K hζ g ∈ SourceKPAdelicBaseCompactMatrix K hζ := by
  constructor
  · intro P
    change sourceKPAdeleMatrixAt K P ((sourceKPGL2ProductEquiv K
      (sourceKPAdelicIwasawaCompact K hζ g)).2) ∈ sourceKPIntegralGroup (sourceKPFiniteVal K P)
    rw [sourceKPAdelicIwasawaCompact, MulEquiv.apply_symm_apply]
    exact sourceKPAdeleIwasawaIntegral_mem K _ P
  · intro v
    change sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K
      ((sourceKPGL2ProductEquiv K (sourceKPAdelicIwasawaCompact K hζ g)).1) v) ∈ _
    rw [sourceKPAdelicIwasawaCompact, MulEquiv.apply_symm_apply, sourceKPArchIwasawaCompact_at]
    exact ⟨_, rfl⟩

theorem sourceKPGL2ProductEquiv_scalar (a : 𝔸[K]ˣ) :
    sourceKPGL2ProductEquiv K (GeneralLinearGroup.scalar (Fin 2) a) =
      (GeneralLinearGroup.scalar (Fin 2) (Units.map (RingHom.fst _ _).toMonoidHom a),
       GeneralLinearGroup.scalar (Fin 2) (Units.map (RingHom.snd _ _).toMonoidHom a)) := by
  apply Prod.ext <;> exact GeneralLinearGroup.map_scalar _ _

theorem sourceKPAdelicIwasawa_factor (g : GL (Fin 2) 𝔸[K]) :
    g = sourceKPAdelicIwasawaBorel K hζ g *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPAdelicIwasawaScalar K hζ g) *
        sourceKPAdelicIwasawaCompact K hζ g := by
  apply (sourceKPGL2ProductEquiv K).injective
  rw [map_mul, map_mul, sourceKPAdelicIwasawaBorel, sourceKPAdelicIwasawaCompact,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, sourceKPGL2ProductEquiv_scalar]
  apply Prod.ext
  · change (sourceKPGL2ProductEquiv K g).1 = sourceKPArchIwasawaBorel K hζ _ *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPArchIwasawaScalar K hζ _) * sourceKPArchIwasawaCompact K hζ _
    exact sourceKPArchIwasawa_factor K hζ _
  · change (sourceKPGL2ProductEquiv K g).2 = sourceKPAdeleIwasawaBorel K _ *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPAdeleIwasawaScalar K _) * sourceKPAdeleIwasawaIntegral K _
    exact sourceKPAdeleIwasawa_factor K _

theorem sourceKPAdelicIwasawaBorel_complex (g : GL (Fin 2) 𝔸[K]) (v : InfinitePlace K) :
    sourceKPAdelicBaseComplexAt K hζ v (sourceKPAdelicIwasawaBorel K hζ g) =
      sourceArchIwasawaBorel (sourceKPAdelicBaseComplexAt K hζ v g) := by
  change sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K
    ((sourceKPGL2ProductEquiv K (sourceKPAdelicIwasawaBorel K hζ g)).1) v) = _
  rw [sourceKPAdelicIwasawaBorel, MulEquiv.apply_symm_apply, sourceKPArchIwasawaBorel_at]
  rfl

theorem sourceKPAdelicIwasawaBorel_finite (g : GL (Fin 2) 𝔸[K])
    (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdelicBaseFiniteAt K P (sourceKPAdelicIwasawaBorel K hζ g) =
      (sourceKPLocalIwasawa K P (sourceKPAdelicBaseFiniteAt K P g)).borel := by
  change sourceKPAdeleMatrixAt K P
    ((sourceKPGL2ProductEquiv K (sourceKPAdelicIwasawaBorel K hζ g)).2) = _
  rw [sourceKPAdelicIwasawaBorel, MulEquiv.apply_symm_apply, sourceKPAdeleIwasawaBorel_at]
  rfl

theorem sourceKPAdelicIwasawaBorel_eventually_one (g : GL (Fin 2) 𝔸[K]) :
    ∀ᶠ P in Filter.cofinite,
      sourceKPAdelicBaseFiniteAt K P (sourceKPAdelicIwasawaBorel K hζ g) = 1 := by
  filter_upwards [sourceKPAdeleMatrixAt_eventually_integral K (sourceKPGL2ProductEquiv K g).2] with P hP
  rw [sourceKPAdelicIwasawaBorel_finite]
  exact (sourceKPLocalIwasawa_of_integral K P _ hP).1

theorem sourceKPAdelicIwasawa_arch_torus_norm (g : GL (Fin 2) 𝔸[K]) (v : InfinitePlace K) :
    ‖(GeneralLinearGroup.det (sourceKPAdelicBaseComplexAt K hζ v
      (sourceKPAdelicIwasawaBorel K hζ g)) : ℂ)‖ =
        sourceArchHeight (sourceKPAdelicBaseComplexAt K hζ v g) := by
  rw [sourceKPAdelicIwasawaBorel_complex]
  exact sourceArchIwasawa_torus_norm _

theorem sourceKPAdelicIwasawa_finite_torus_norm (g : GL (Fin 2) 𝔸[K])
    (P : HeightOneSpectrum (𝓞 K)) :
    ‖(GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt K P
      (sourceKPAdelicIwasawaBorel K hζ g)) : P.adicCompletion K)‖ =
      ‖(GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt K P g) : P.adicCompletion K)‖ /
        max ‖sourceKPAdelicBaseFiniteAt K P g 1 0‖ ‖sourceKPAdelicBaseFiniteAt K P g 1 1‖ ^ 2 := by
  rw [sourceKPAdelicIwasawaBorel_finite]
  exact sourceKPLocalIwasawa_torus_norm K P _

theorem sourceKPAdelicBaseIwasawa (g : PGL(2, 𝔸[K])) :
    ∃ b ∈ sourceKPRingBorel 𝔸[K], ∃ k ∈ sourceKPAdelicBaseCompact K hζ, g = b * k := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective g
  refine ⟨ProjGenLinGroup.mk (sourceKPAdelicIwasawaBorel K hζ g),
    ⟨_, sourceKPAdelicIwasawaBorel_mem K hζ g, rfl⟩,
    ProjGenLinGroup.mk (sourceKPAdelicIwasawaCompact K hζ g),
    ⟨_, sourceKPAdelicIwasawaCompact_mem K hζ g, rfl⟩, ?_⟩
  conv_lhs => rw [sourceKPAdelicIwasawa_factor K hζ g]
  rw [map_mul, map_mul, ProjGenLinGroup.mk_scalar, mul_one]

end
end ArtinMatthews
