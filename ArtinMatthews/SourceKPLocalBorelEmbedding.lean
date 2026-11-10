module

public import ArtinMatthews.SourceKPAdelicPrincipalSeries
import ArtinMatthews.SourceAdelicIwasawaAssembly
public import ArtinMatthews.SourceFiniteKPProjectiveBorel
public import ArtinMatthews.SourceKPAdeleLocalCover
public import ArtinMatthews.SourceKPExteriorUpperCompatibility
public import ArtinMatthews.SourceKPProjectiveSections
public import ArtinMatthews.SourceKubotaCocycle
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual local normalized Borel embeds in the global covering
Borel, with its diagonal section and compact cochain unchanged. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPAdeleSingleMatrix_diagonal (y : (P.adicCompletion K)ˣ) :
    sourceKPAdeleSingleMatrix K P (sourceGL2Diagonal y) =
      sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPAdeleLocalUnit K P y) := by
  apply sourceKPAdeleMatrixAt_ext K
  intro Q
  rw [sourceKPAdeleMatrixAt_diagonal]
  by_cases hQP : Q = P
  · subst Q
    rw [sourceKPAdeleSingleMatrix_same, sourceKPAdeleLocalUnit_same]
  · rw [sourceKPAdeleSingleMatrix_other K P Q hQP, sourceKPAdeleLocalUnit_other K P y Q hQP]
    exact (sourceGL2DiagonalHom (Q.adicCompletion K)).map_one.symm

theorem sourceKPAdelicLocalProjective_diagonal (y : (P.adicCompletion K)ˣ) :
    sourceKPAdelicLocalProjective K hζ P
      (sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal y)) =
      sourceKPAdelicProjectiveDiagonalLift K hζ (IdeleGroup.ofAdicCompletion (𝓞 K) K P y) := by
  apply Prod.ext
  · change 1 = sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K)
      (sourceKPIdeleInfiniteUnit K (IdeleGroup.ofAdicCompletion (𝓞 K) K P y))
    change 1 = sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) 1
    exact (map_one _).symm
  · change sourceKPFiniteAdeleProjectiveMk K hζ
        (sourceKPAdeleLocalCover K hζ P (sourceFiniteKP2Lift K hζ P (sourceGL2Diagonal y))) =
      sourceKPFiniteAdeleProjectiveMk K hζ
        ⟨1, sourceKPDiagonalHom 𝔸ᶠ[K] (sourceKPAdeleLocalUnit K P y)⟩
    apply congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
    apply SourceKPFiniteAdeleCover.ext
    · change (sourceKPRootsTransport K hζ P).symm
        (1 / sourceKPFinitePhase K hζ P (sourceGL2Diagonal y)) = 1
      rw [sourceKPFinitePhase_diagonal, div_one, map_one]
    · exact sourceKPAdeleSingleMatrix_diagonal K P y

theorem sourceFiniteKPProjectiveBorel_factor (b : SourceFiniteKPProjectiveBorel K hζ P) :
    ∃ (z : rootsOfUnity 3 (P.adicCompletion K)) (x : P.adicCompletion K)
      (y : (P.adicCompletion K)ˣ),
      b.val = sourceFiniteKP2ProjectiveCenter K hζ P z *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x) *
          sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal y) := by
  obtain ⟨a, rfl⟩ := (sourceFiniteKPProjectiveBorelEquiv K hζ P).surjective b
  have hbase := sourceGL2NormalizedBorel_factor (P.adicCompletion K) a.val.base a.property
  have hc : a.val = sourceFiniteKP2Center K hζ P a.val.central *
      sourceFiniteKP2Lift K hζ P a.val.base := by
    apply SourceFiniteKP2Cover.ext
    · change a.val.central = a.val.central * 1 * sourceFiniteKP2Multiplier K hζ P 1 a.val.base
      rw [sourceFiniteKP2Multiplier_one_left, mul_one, mul_one]
    · change a.val.base = 1 * a.val.base
      rw [one_mul]
  refine ⟨a.val.central, a.val.base 0 1, GeneralLinearGroup.det a.val.base, ?_⟩
  change sourceFiniteKP2ProjectiveMk K hζ P a.val = _
  calc
    sourceFiniteKP2ProjectiveMk K hζ P a.val =
        sourceFiniteKP2ProjectiveMk K hζ P (sourceFiniteKP2Center K hζ P a.val.central *
          sourceFiniteKP2Lift K hζ P a.val.base) :=
      congrArg (sourceFiniteKP2ProjectiveMk K hζ P) hc
    _ = sourceFiniteKP2ProjectiveCenter K hζ P a.val.central *
        sourceFiniteKP2ProjectiveLift K hζ P a.val.base := by rw [map_mul]; rfl
    _ = sourceFiniteKP2ProjectiveCenter K hζ P a.val.central *
        sourceFiniteKP2ProjectiveLift K hζ P
          (sourceGL2Upper (a.val.base 0 1) * sourceGL2Diagonal (GeneralLinearGroup.det a.val.base)) :=
      congrArg (fun g => sourceFiniteKP2ProjectiveCenter K hζ P a.val.central *
        sourceFiniteKP2ProjectiveLift K hζ P g) hbase
    _ = _ := by
      rw [← sourceFiniteKP2ProjectiveLift_mul_of_phase_one K hζ P _ _
        (sourceFiniteKP2Multiplier_root_diagonal K hζ P _ _).1, ← mul_assoc]

theorem sourceKPAdelicLocalProjective_borel_mem (b : SourceFiniteKPProjectiveBorel K hζ P) :
    sourceKPAdelicLocalProjective K hζ P b.val ∈ sourceKPAdelicCoveringBorel K hζ := by
  obtain ⟨z, x, y, hb⟩ := sourceFiniteKPProjectiveBorel_factor K hζ P b
  rw [hb, map_mul, map_mul, sourceKPAdelicLocalProjective_center,
    sourceKPAdelicLocalProjective_upper, sourceKPAdelicLocalProjective_diagonal]
  apply (sourceKPAdelicCoveringBorel K hζ).mul_mem
  · exact (sourceKPAdelicCoveringBorel K hζ).mul_mem
      (sourceKPAdelicCoveringTorus_le_borel K hζ
        (sourceKPAdelicCoveringTorus_center_mem K hζ _))
      (sourceKPAdelicCoveringBorel_upper_mem K hζ _)
  · exact sourceKPAdelicCoveringTorus_le_borel K hζ
      (sourceKPAdelicCoveringTorus_diagonal_mem K hζ _)

def sourceKPAdelicLocalBorel : SourceFiniteKPProjectiveBorel K hζ P →*
    sourceKPAdelicCoveringBorel K hζ where
  toFun b := ⟨sourceKPAdelicLocalProjective K hζ P b.val,
    sourceKPAdelicLocalProjective_borel_mem K hζ P b⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' b c := Subtype.ext (map_mul _ b.val c.val)

theorem sourceKPAdelicLocalBorel_val (b : SourceFiniteKPProjectiveBorel K hζ P) :
    (sourceKPAdelicLocalBorel K hζ P b).val = sourceKPAdelicLocalProjective K hζ P b.val := rfl

def sourceKPAdelicLocalBorelRepresentation (s : ℂ) :
    Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) (SourceKPAdelicTorusInducedSpace K hζ s) :=
  (sourceKPAdelicNormalizedBorelRepresentation K hζ s).comp (sourceKPAdelicLocalBorel K hζ P)

end
end ArtinMatthews
