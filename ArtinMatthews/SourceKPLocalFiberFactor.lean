module

public import ArtinMatthews.SourceKPLocalRestBase
public import ArtinMatthews.SourceKPExteriorUpperCompatibility
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

/-! The actual adelic upper fiber is a local Weyl-upper factor times
the remaining global factor. The Weyl commutation uses the exact cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPLocalWeylRest_base :
    sourceKPAdelicLocalBase K hζ P
      ((sourceKPAdelicLocalProjective K hζ P
        (sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl))⁻¹ *
          sourceKPAdelicProjectiveWeyl K hζ) = 1 := by
  rw [map_mul, map_inv, sourceKPAdelicLocalBase_local, sourceKPAdelicLocalBase_weyl]
  change (ProjGenLinGroup.mk (sourceGL2Weyl : GL (Fin 2) (P.adicCompletion K)))⁻¹ *
    ProjGenLinGroup.mk sourceGL2Weyl = 1
  exact inv_mul_cancel _

theorem sourceKPLocalFiber_factor (x : P.adicCompletion K) (r : 𝔸ᶠ[K])
    (g : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ
        (0, sourceKPFiniteAdditiveSingle K P x + r) * g =
      sourceKPAdelicLocalProjective K hζ P
        (sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl *
          sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x)) *
        sourceKPLocalFiberRest K hζ P r g := by
  let d := sourceKPAdelicLocalProjective K hζ P
    (sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl)
  let n := sourceKPAdelicLocalProjective K hζ P
    (sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x))
  let w := d⁻¹ * sourceKPAdelicProjectiveWeyl K hζ
  let m : SourceKPAdelicProjective K hζ := sourceKPAdelicUpperLift K hζ (0,r)
  have hw : sourceKPAdelicLocalBase K hζ P w = 1 := sourceKPLocalWeylRest_base K hζ P
  have hc : Commute n w := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P _ w hw
  have hn : n = sourceKPAdelicUpperLift K hζ
      (0, sourceKPFiniteAdditiveSingle K P x) :=
    sourceKPAdelicLocalProjective_upper K hζ P x
  have hupper : sourceKPAdelicUpperLift K hζ
      (0, sourceKPFiniteAdditiveSingle K P x + r) =
      n * m := by
    have hh := (sourceKPFiniteUpperHom K hζ).map_mul
      (Multiplicative.ofAdd (sourceKPFiniteAdditiveSingle K P x)) (Multiplicative.ofAdd r)
    change sourceKPAdelicUpperLift K hζ (0, sourceKPFiniteAdditiveSingle K P x + r) =
      sourceKPAdelicUpperLift K hζ (0, sourceKPFiniteAdditiveSingle K P x) * m at hh
    exact hh.trans (congrArg (fun q => q*m) hn.symm)
  have hW : sourceKPAdelicProjectiveWeyl K hζ = d*w := by
    dsimp only [w]
    rw [mul_inv_cancel_left]
  have hd : sourceKPAdelicLocalProjective K hζ P
      (sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x)) = d*n := map_mul _ _ _
  change sourceKPAdelicProjectiveWeyl K hζ *
      sourceKPAdelicUpperLift K hζ (0, sourceKPFiniteAdditiveSingle K P x + r) * g =
    sourceKPAdelicLocalProjective K hζ P
      (sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x)) * (w*m*g)
  calc
    _ = sourceKPAdelicProjectiveWeyl K hζ * (n*m) * g :=
      congrArg (fun q => sourceKPAdelicProjectiveWeyl K hζ*q*g) hupper
    _ = (d*w)*(n*m)*g := congrArg (fun q => q*(n*m)*g) hW
    _ = (d*n)*(w*m*g) := by
      simpa only [mul_assoc] using congrArg (fun a => d*a*m*g) hc.eq.symm
    _ = _ := congrArg (fun q => q*(w*m*g)) hd.symm

end
end ArtinMatthews
