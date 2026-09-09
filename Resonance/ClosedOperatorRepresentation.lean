import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! The nonnegative selfadjoint square of an actual densely defined closed
operator.  The proof constructs the resolvent through orthogonal projection
onto the actual L² graph.  Existence of a representing selfadjoint operator,
surjectivity of its resolvent, and density of the square domain are not
assumptions. -/
open Set Filter RCLike LinearPMap WithLp
open scoped Topology ComplexConjugate
namespace Resonance.ClosedOperatorRepresentation
noncomputable section
variable {𝕜 E F:Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

def squareDomain (T:E→ₗ.[𝕜]F) : Submodule 𝕜 E where
  carrier := {x | ∃hx:x∈T.domain,T ⟨x,hx⟩∈T†.domain}
  zero_mem' := ⟨T.domain.zero_mem,by
    change T (0:T.domain)∈T†.domain
    rw [LinearPMap.map_zero]
    exact T†.domain.zero_mem⟩
  add_mem' := by
    rintro x y ⟨hx,hTx⟩ ⟨hy,hTy⟩
    refine ⟨T.domain.add_mem hx hy,?_⟩
    have h := T†.domain.add_mem hTx hTy
    simpa only [←LinearPMap.map_add] using h
  smul_mem' := by
    rintro c x ⟨hx,hTx⟩
    refine ⟨T.domain.smul_mem c hx,?_⟩
    have h := T†.domain.smul_mem c hTx
    simpa only [←LinearPMap.map_smul] using h

def squareDomainInclusion (T:E→ₗ.[𝕜]F) : squareDomain T→ₗ[𝕜]T.domain where
  toFun x := ⟨x,x.prop.choose⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def squareImage (T:E→ₗ.[𝕜]F) : squareDomain T→ₗ[𝕜]T†.domain :=
  (T.toFun.comp (squareDomainInclusion T)).codRestrict T†.domain
    (fun x=>x.prop.choose_spec)

def square (T:E→ₗ.[𝕜]F) : E→ₗ.[𝕜]E where
  domain := squareDomain T
  toFun := T†.toFun.comp (squareImage T)

theorem square_domain_iff (T:E→ₗ.[𝕜]F) (x:E) :
    x∈(square T).domain↔∃hx:x∈T.domain,T ⟨x,hx⟩∈T†.domain := Iff.rfl

theorem square_pairing (T:E→ₗ.[𝕜]F) (hT:Dense (T.domain:Set E))
    (x:(square T).domain) (y:T.domain) :
    ⟪square T x,(y:E)⟫=⟪T (squareDomainInclusion T x),T y⟫ :=
  LinearPMap.adjoint_isFormalAdjoint hT (squareImage T x) y

theorem square_isFormalAdjoint (T:E→ₗ.[𝕜]F) (hT:Dense (T.domain:Set E)) :
    (square T).IsFormalAdjoint (square T) := by
  intro x y
  have hx := square_pairing T hT x (squareDomainInclusion T y)
  have hy := square_pairing T hT y (squareDomainInclusion T x)
  change ⟪square T x,(y:E)⟫=_ at hx
  change ⟪square T y,(x:E)⟫=_ at hy
  rw [hx,←inner_conj_symm (x:E) (square T y),hy,inner_conj_symm]

theorem square_nonnegative (T:E→ₗ.[𝕜]F) (hT:Dense (T.domain:Set E))
    (x:(square T).domain) : 0≤RCLike.re ⟪square T x,(x:E)⟫ := by
  change 0≤RCLike.re ⟪square T x,(squareDomainInclusion T x:E)⟫
  rw [square_pairing T hT x (squareDomainInclusion T x)]
  exact inner_self_nonneg

/-- Exact variational characterization on the whole form domain.  The
displayed right side is derived, not imposed as a representation axiom. -/
theorem square_graph_iff (T:E→ₗ.[𝕜]F) (hT:Dense (T.domain:Set E)) (x z:E) :
    (x,z)∈(square T).graph ↔
      ∃hx:x∈T.domain,∀y:T.domain,⟪z,(y:E)⟫=⟪T ⟨x,hx⟩,T y⟫ := by
  constructor
  · intro hg
    obtain ⟨u,hu,hval⟩ := ((square T).mem_graph_iff).mp hg
    change (u:E)=x at hu
    change square T u=z at hval
    have hx : x∈T.domain := by
      rw [←hu]
      exact u.prop.choose
    refine ⟨hx,fun y=>?_⟩
    have he := square_pairing T hT u y
    rw [hval] at he
    convert he using 1
    congr 2
    exact Subtype.ext hu.symm
  · rintro ⟨hx,he⟩
    have had : T ⟨x,hx⟩∈T†.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨z,he⟩
    let u:(square T).domain := ⟨x,⟨hx,had⟩⟩
    have hval : square T u=z := LinearPMap.adjoint_apply_eq hT _ he
    exact ((square T).mem_graph_iff).mpr ⟨u,rfl,hval⟩

def graphHilbert (T:E→ₗ.[𝕜]F) : Submodule 𝕜 (WithLp 2 (E×F)) :=
  T.graph.comap (WithLp.linearEquiv 2 𝕜 (E×F)).toLinearMap

omit [CompleteSpace E] in
theorem graphHilbert_isClosed (T:E→ₗ.[𝕜]F) (hclosed:T.IsClosed) :
    IsClosed (graphHilbert T:Set (WithLp 2 (E×F))) :=
  hclosed.preimage (WithLp.prod_continuous_ofLp 2 E F)

/-- The domain density required by the adjoint is itself a consequence
of formal symmetry and the constructed resolvent range. -/
theorem symmetric_surjective_dense (A:E→ₗ.[𝕜]E)
    (hformal:A.IsFormalAdjoint A)
    (hsurj:∀f:E,∃x:A.domain,(x:E)+A x=f) : Dense (A.domain:Set E) := by
  have ho : A.domainᗮ=⊥ := by
    apply bot_unique
    intro v hv
    obtain ⟨x,hx⟩ := hsurj v
    have hx0 : (x:E)=0 := by
      apply (inner_self_eq_zero (𝕜:=𝕜)).mp
      obtain ⟨z,hz⟩ := hsurj (x:E)
      calc
        ⟪(x:E),(x:E)⟫ = ⟪(x:E),(z:E)+A z⟫ := by rw [hz]
        _ = ⟪(x:E)+A x,(z:E)⟫ := by
          rw [inner_add_right,inner_add_left,hformal x z]
        _ = ⟪v,(z:E)⟫ := by rw [hx]
        _ = 0 := (A.domain.mem_orthogonal' v).mp hv z z.prop
    have hxz : x=0 := Subtype.ext hx0
    have hv0 : v=0 := by
      rw [←hx,hxz]
      change (0:E)+A (0:A.domain)=0
      rw [LinearPMap.map_zero,add_zero]
    exact hv0
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [←Submodule.orthogonal_orthogonal_eq_closure,ho,Submodule.bot_orthogonal_eq_top]

/-- A symmetric partial operator with surjective `I+A` equals its actual
adjoint.  This excludes the adjoint's nondense-domain fallback. -/
theorem symmetric_surjective_selfAdjoint (A:E→ₗ.[𝕜]E)
    (hformal:A.IsFormalAdjoint A)
    (hsurj:∀f:E,∃x:A.domain,(x:E)+A x=f) : IsSelfAdjoint A := by
  have hd := symmetric_surjective_dense A hformal hsurj
  have hadj := LinearPMap.adjoint_isFormalAdjoint hd
  have hback (y:A†.domain) : ∃x:A.domain,(x:E)=(y:E) ∧ A x=A† y := by
    obtain ⟨x,hx⟩ := hsurj ((y:E)+A† y)
    have hxy : (x:E)=(y:E) := by
      apply ext_inner_right 𝕜
      intro v
      obtain ⟨z,hz⟩ := hsurj v
      rw [←hz,inner_add_right,inner_add_right,←hformal x z,←hadj y z,
        ←inner_add_left,←inner_add_left,hx]
    refine ⟨x,hxy,?_⟩
    apply add_left_cancel (a:=(y:E))
    simpa only [hxy] using hx
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply le_antisymm
  · refine ⟨?_,?_⟩
    · intro y hy
      obtain ⟨x,hx,_⟩ := hback ⟨y,hy⟩
      change (x:E)=y at hx
      rw [←hx]
      exact x.prop
    · intro x y hxy
      obtain ⟨u,hu,hval⟩ := hback x
      rw [←hval]
      congr 1
      exact Subtype.ext (hu.trans hxy)
  · exact LinearPMap.IsFormalAdjoint.le_adjoint hd hformal

variable [CompleteSpace F]

/-- Projection of `(f,0)` onto the actual closed graph constructs a
solution of `u + T†Tu = f`. -/
theorem square_resolvent_surjective (T:E→ₗ.[𝕜]F)
    (hT:Dense (T.domain:Set E)) (hclosed:T.IsClosed) (f:E) :
    ∃u:(square T).domain,(u:E)+square T u=f := by
  let K := graphHilbert T
  letI : CompleteSpace K := (graphHilbert_isClosed T hclosed).isComplete.completeSpace_coe
  let q : WithLp 2 (E×F) := toLp 2 (f,0)
  let p : WithLp 2 (E×F) := K.starProjection q
  have hp : p∈K := K.starProjection_apply_mem q
  have hpg : ofLp p∈T.graph := hp
  obtain ⟨u,hu,hTu⟩ := (T.mem_graph_iff (x:=ofLp p)).mp hpg
  have hres : q-p∈Kᗮ := K.sub_starProjection_mem_orthogonal q
  have he (x:T.domain) : ⟪f-(u:E),(x:E)⟫=⟪T u,T x⟫ := by
    have hx : toLp 2 ((x:E),T x)∈K := T.mem_graph x
    have hh := (K.mem_orthogonal' (q-p)).mp hres _ hx
    have hh' : ⟪f-(u:E),(x:E)⟫-⟪T u,T x⟫=0 := by
      simpa only [prod_inner_apply,ofLp_sub,ofLp_toLp,Prod.fst_sub,Prod.snd_sub,
        Prod.fst_zero,Prod.snd_zero,←hu,←hTu,zero_sub,inner_neg_left,
        ←sub_eq_add_neg,q] using hh
    exact sub_eq_zero.mp hh'
  have had : T u∈T†.domain := LinearPMap.mem_adjoint_domain_of_exists _ ⟨f-u,he⟩
  let v : (square T).domain := ⟨u,⟨u.prop,had⟩⟩
  have hval : square T v=f-u := LinearPMap.adjoint_apply_eq hT _ he
  exact ⟨v,by change (u:E)+square T v=f; rw [hval]; abel⟩

/-- The actual maximal adjoint square is nonnegative selfadjoint; neither
the operator nor its square is replaced by a bounded surrogate. -/
theorem square_selfAdjoint (T:E→ₗ.[𝕜]F)
    (hT:Dense (T.domain:Set E)) (hclosed:T.IsClosed) : IsSelfAdjoint (square T) :=
  symmetric_surjective_selfAdjoint (square T) (square_isFormalAdjoint T hT)
    (square_resolvent_surjective T hT hclosed)

theorem square_dense_domain (T:E→ₗ.[𝕜]F)
    (hT:Dense (T.domain:Set E)) (hclosed:T.IsClosed) :
    Dense ((square T).domain:Set E) := (square_selfAdjoint T hT hclosed).dense_domain

theorem square_isClosed (T:E→ₗ.[𝕜]F)
    (hT:Dense (T.domain:Set E)) (hclosed:T.IsClosed) : (square T).IsClosed :=
  (square_selfAdjoint T hT hclosed).isClosed

/-- Full nonnegative selfadjoint representation for a densely defined
closed map between Hilbert spaces, with the exact variational graph. -/
theorem closed_dense_operator_representation (T:E→ₗ.[𝕜]F)
    (hT:Dense (T.domain:Set E)) (hclosed:T.IsClosed) :
    IsSelfAdjoint (square T) ∧
    (∀x:(square T).domain,0≤RCLike.re ⟪square T x,(x:E)⟫) ∧
    (∀x z:E,(x,z)∈(square T).graph ↔
      ∃hx:x∈T.domain,∀y:T.domain,⟪z,(y:E)⟫=⟪T ⟨x,hx⟩,T y⟫) :=
  ⟨square_selfAdjoint T hT hclosed,square_nonnegative T hT,square_graph_iff T hT⟩

end
end Resonance.ClosedOperatorRepresentation
