module

public import ArtinMatthews.SourceKPAdelicOutgoingContinuedCompactCarrier
public import ArtinMatthews.SourceKPLocalRestBase


set_option backward.privateInPublic true
@[expose] public section

/-! The actual simultaneous retained lift has exactly the selected
local projections. Every full adelic cover input is reached by a
retained tuple and an exterior remainder with those projections one. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "G" => SourceKPAdelicProjective K hζ
local notation "i₀" => sourceKPAdelicLocalProjective K hζ
local notation "base" => sourceKPAdelicLocalBase K hζ

theorem sourceKPAdelicOutgoingLocalBase_other (P Q : Pr) (h : Q ≠ P)
    (g : SourceFiniteKP2Projective K hζ P) : base Q (i₀ P g) = 1 := by
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range g
  change ProjGenLinGroup.mk (sourceKPAdeleMatrixAt K Q (sourceKPAdeleSingleMatrix K P a.base)) = 1
  rw [sourceKPAdeleSingleMatrix_other K P Q h,map_one]

variable (places : Finset (HeightOneSpectrum (𝓞 K)))

local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ places
local notation "Rest" => SourceKPAdelicOutgoingRetainedRest K hζ places
local notation "L" => sourceKPLocalCompactProductLift K hζ places
local notation "Lᴮ" => sourceKPLocalCompactProductBorelLift K hζ places
local notation "LocalGroup" => (fun Q : ↥places => SourceFiniteKP2Projective K hζ (Subtype.val Q))
local notation "LocalBorel" => (fun Q : ↥places => SourceFiniteKPProjectiveBorel K hζ (Subtype.val Q))

theorem sourceKPAdelicOutgoingRetainedLift_single (P : ↥places) (g : LocalGroup P) :
    L (Pi.mulSingle (M := LocalGroup) P g) = i₀ P.val g := by
  unfold sourceKPLocalCompactProductLift
  exact MonoidHom.noncommPiCoprod_mulSingle (fun Q : ↥places => i₀ Q.val) P g

theorem sourceKPAdelicOutgoingRetainedBorelLift_single (P : ↥places) (b : LocalBorel P) :
    Lᴮ (Pi.mulSingle (M := LocalBorel) P b) = sourceKPAdelicLocalBorel K hζ P.val b := by
  unfold sourceKPLocalCompactProductBorelLift
  exact MonoidHom.noncommPiCoprod_mulSingle (fun Q : ↥places => sourceKPAdelicLocalBorel K hζ Q.val) P b

theorem sourceKPAdelicOutgoingRetainedLift_localBase (g : Gₛ) (P : ↥places) :
    base P.val (L g) = sourceFiniteKP2ProjectiveProjection K hζ P.val (g P) := by
  let q : Gₛ →* PGL(2, P.val.adicCompletion K) := (base P.val).comp L
  let p : Gₛ →* PGL(2, P.val.adicCompletion K) :=
    (sourceFiniteKP2ProjectiveProjection K hζ P.val).comp
      (Pi.evalMonoidHom LocalGroup P)
  have he : q = p := by
    apply MonoidHom.pi_ext
    intro Q a
    change base P.val (L (Pi.mulSingle (M := LocalGroup) Q a)) =
      sourceFiniteKP2ProjectiveProjection K hζ P.val (Pi.mulSingle (M := LocalGroup) Q a P)
    rw [sourceKPAdelicOutgoingRetainedLift_single K hζ places Q a]
    by_cases h : P = Q
    · subst Q
      rw [Pi.mulSingle_eq_same,sourceKPAdelicLocalBase_local K hζ P.val a]
    · rw [Pi.mulSingle_eq_of_ne h,map_one]
      exact sourceKPAdelicOutgoingLocalBase_other K hζ Q.val P.val
        (fun he => h (Subtype.ext he)) a
  exact congrArg (fun f : Gₛ →* PGL(2, P.val.adicCompletion K) => f g) he

def sourceKPAdelicOutgoingRetainedEval (q : Gₛ × Rest) : G :=
  L q.1*q.2.val

local notation "ev" => sourceKPAdelicOutgoingRetainedEval K hζ places

theorem sourceKPAdelicOutgoingRetainedEval_surjective : Function.Surjective ev := by
  intro g
  choose v hv using fun P : ↥places =>
    sourceFiniteKP2ProjectiveProjection_surjective K hζ P.val (base P.val g)
  let r := (L v)⁻¹*g
  have hr (P : ↥places) : base P.val r = 1 := by
    change base P.val ((L v)⁻¹*g) = 1
    rw [map_mul (base P.val),map_inv (base P.val),
      sourceKPAdelicOutgoingRetainedLift_localBase K hζ places v P,hv P,inv_mul_cancel]
  exact ⟨(v,⟨r,hr⟩),mul_inv_cancel_left (L v) g⟩

theorem sourceKPAdelicOutgoingRetainedEval_right (q : Gₛ × Rest) (g : Gₛ) :
    ev q*L g = ev (q.1*g,q.2) := by
  have hc := sourceKPLocalCompactProductLift_commute_of_base_one K hζ places g q.2.val q.2.property
  calc
    ev q*L g = L q.1*(q.2.val*L g) := mul_assoc _ _ _
    _ = L q.1*(L g*q.2.val) := congrArg (fun u : G => L q.1*u) hc.eq.symm
    _ = ev (q.1*g,q.2) := by rw [sourceKPAdelicOutgoingRetainedEval,map_mul L,mul_assoc]

end
end ArtinMatthews
