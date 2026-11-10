module

public import ArtinMatthews.SixthKummerSharpModulus
public import ArtinMatthews.SourceKPLocalRestCommute
public import ArtinMatthews.SourceKPAdeleFiniteKernel
public import ArtinMatthews.SourceKPLocalRestBase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Finite products of actual local lifts, including the places above
six. Their projective coordinates and archimedean component are exact. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

def sourceKPCoupledLocalProduct :
    ((P : S) → SourceFiniteKP2Projective K hζ P.val) →* SourceKPAdelicProjective K hζ :=
  MonoidHom.noncommPiCoprod (fun P : S => sourceKPAdelicLocalProjective K hζ P.val) (by
    intro P Q hPQ g h
    exact sourceKPAdelicLocalProjective_commute K hζ P.val Q.val
      (fun he => hPQ (Subtype.ext he.symm)) g h)

theorem sourceKPCoupledLocalProduct_single (P : S) (g : SourceFiniteKP2Projective K hζ P.val) :
    sourceKPCoupledLocalProduct K hζ S (Pi.mulSingle P g) = sourceKPAdelicLocalProjective K hζ P.val g :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem sourceKPCoupledLocalProduct_at (P : S) (f : (Q : S) → SourceFiniteKP2Projective K hζ Q.val) :
    sourceKPAdelicLocalBase K hζ P.val (sourceKPCoupledLocalProduct K hζ S f) =
      sourceFiniteKP2ProjectiveProjection K hζ P.val (f P) := by
  have he : (sourceKPAdelicLocalBase K hζ P.val).comp (sourceKPCoupledLocalProduct K hζ S) =
      (sourceFiniteKP2ProjectiveProjection K hζ P.val).comp (Pi.evalMonoidHom _ P) := by
    apply MonoidHom.pi_ext
    intro Q g
    change sourceKPAdelicLocalBase K hζ P.val (sourceKPCoupledLocalProduct K hζ S (Pi.mulSingle Q g)) =
      sourceFiniteKP2ProjectiveProjection K hζ P.val
        (Pi.mulSingle (M := fun R : S => SourceFiniteKP2Projective K hζ R.val) Q g P)
    rw [sourceKPCoupledLocalProduct_single]
    by_cases hQP : P = Q
    · subst Q
      rw [sourceKPAdelicLocalBase_local, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hQP, map_one]
      exact sourceKPAdelicProjectiveAt_local_other K hζ P.val Q.val
        (fun h => hQP (Subtype.ext h)) g
  exact DFunLike.congr_fun he f

theorem sourceKPCoupledLocalProduct_outside (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S)
    (f : (Q : S) → SourceFiniteKP2Projective K hζ Q.val) :
    sourceKPAdelicLocalBase K hζ P (sourceKPCoupledLocalProduct K hζ S f) = 1 := by
  have he : (sourceKPAdelicLocalBase K hζ P).comp (sourceKPCoupledLocalProduct K hζ S) = 1 := by
    apply MonoidHom.pi_ext
    intro Q g
    change sourceKPAdelicLocalBase K hζ P (sourceKPCoupledLocalProduct K hζ S (Pi.mulSingle Q g)) = 1
    rw [sourceKPCoupledLocalProduct_single]
    exact sourceKPAdelicProjectiveAt_local_other K hζ P Q.val
      (fun h => hP (h ▸ Q.property)) g
  exact DFunLike.congr_fun he f

theorem sourceKPCoupledLocalProduct_arch (f : (Q : S) → SourceFiniteKP2Projective K hζ Q.val) :
    (sourceKPCoupledLocalProduct K hζ S f).1 = 1 := by
  have he : (MonoidHom.fst (PGL(2, InfiniteAdeleRing K)) (SourceKPFiniteAdeleProjective K hζ)).comp
      (sourceKPCoupledLocalProduct K hζ S) = 1 := by
    apply MonoidHom.pi_ext
    intro Q g
    change (sourceKPCoupledLocalProduct K hζ S (Pi.mulSingle Q g)).1 = 1
    rw [sourceKPCoupledLocalProduct_single]
    rfl
  exact DFunLike.congr_fun he f

def sourceKPCoupledWildWeyl : SourceKPAdelicProjective K hζ :=
  sourceKPCoupledLocalProduct K hζ (sixthWildPrimes K)
    (fun P => sourceFiniteKP2ProjectiveLift K hζ P.val sourceGL2Weyl)

theorem sourceKPCoupledWildWeyl_arch : (sourceKPCoupledWildWeyl K hζ).1 = 1 :=
  sourceKPCoupledLocalProduct_arch K hζ (sixthWildPrimes K) _

theorem sourceKPCoupledWildWeyl_at (P : HeightOneSpectrum (𝓞 K)) (hP : (6 : 𝓞 K) ∈ P.asIdeal) :
    sourceKPAdelicLocalBase K hζ P (sourceKPCoupledWildWeyl K hζ) =
      ProjGenLinGroup.mk (sourceGL2Weyl : GL (Fin 2) (P.adicCompletion K)) :=
  sourceKPCoupledLocalProduct_at K hζ (sixthWildPrimes K) ⟨P, (mem_sixthWildPrimes P).mpr hP⟩ _

theorem sourceKPCoupledWildWeyl_outside (P : HeightOneSpectrum (𝓞 K)) (hP : (6 : 𝓞 K) ∉ P.asIdeal) :
    sourceKPAdelicLocalBase K hζ P (sourceKPCoupledWildWeyl K hζ) = 1 :=
  sourceKPCoupledLocalProduct_outside K hζ (sixthWildPrimes K) P
    (fun h => hP ((mem_sixthWildPrimes P).mp h)) _

end
end ArtinMatthews
