module

public import ArtinMatthews.SourceKPAdelicOutgoingRetainedSlice


set_option backward.privateInPublic true
@[expose] public section

/-! Every finite adelic input has an actual retained tuple and an
exterior finite remainder, for the original fixed retained set. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (places : Finset (HeightOneSpectrum (𝓞 K)))

local notation "G" => SourceKPAdelicProjective K hζ
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ places
local notation "L" => sourceKPLocalCompactProductLift K hζ places
local notation "base" => sourceKPAdelicLocalBase K hζ

abbrev SourceKPAdelicOutgoingRetainedFiniteRest :=
  {qf : Gf // ∀ P : ↥places, base P.val (1,qf) = 1}

local notation "Rest" => SourceKPAdelicOutgoingRetainedFiniteRest K hζ places

def sourceKPAdelicOutgoingRetainedFiniteEval (q : Gₛ × Rest) : Gf :=
  q.2.val * (L q.1).2

local notation "ev" => sourceKPAdelicOutgoingRetainedFiniteEval K hζ places

theorem sourceKPAdelicOutgoingRetainedFiniteEval_surjective : Function.Surjective ev := by
  intro qf
  obtain ⟨⟨g,r⟩,h⟩ := sourceKPAdelicOutgoingRetainedEval_surjective K hζ places ((1,qf) : G)
  change L g*r.val = ((1,qf) : G) at h
  have ha := congrArg (fun u : G => u.1) h
  change (L g).1*r.val.1 = 1 at ha
  rw [sourceKPAdelicOutgoingRetainedLift_arch_one K hζ places, one_mul] at ha
  have hr : ((1,r.val.2) : G) = r.val := Prod.ext ha.symm rfl
  have hbase (P : ↥places) : base P.val (1,r.val.2) = 1 :=
    (congrArg (fun u : G => base P.val u) hr).trans (r.property P)
  refine ⟨(g,⟨r.val.2,hbase⟩),?_⟩
  have hc := sourceKPLocalCompactProductLift_commute_of_base_one K hζ places g r.val r.property
  exact congrArg (fun u : G => u.2) (hc.eq.symm.trans h)

theorem sourceKPAdelicOutgoingRetainedFiniteEval_right (q : Gₛ × Rest) (g : Gₛ) :
    ev q * (L g).2 = ev (q.1*g,q.2) := by
  unfold sourceKPAdelicOutgoingRetainedFiniteEval
  rw [map_mul L]
  change (q.2.val * (L q.1).2) * (L g).2 = q.2.val * ((L q.1).2 * (L g).2)
  exact mul_assoc _ _ _

end
end ArtinMatthews
