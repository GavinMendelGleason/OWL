
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Vec hiding (_∈_)
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)
open import Relation.Binary.Core
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.String
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

module Example where

  data ClassURI : Set where
    OwlThing : ClassURI
    OwlNothing : ClassURI
    AgentURI : ClassURI
    PersonURI : ClassURI 

  data DataPropertyURI : Set where
    OwlTopDataProperty : DataPropertyURI
    OwlBottomDataProperty : DataPropertyURI
    NameURI : DataPropertyURI

  data ObjectPropertyURI : Set where
    OwlTopObjectProperty : ObjectPropertyURI
    OwlBottomObjectProperty : ObjectPropertyURI
    KnowsURI : ObjectPropertyURI

  data DataTypeURI : Set where
    StringURI : DataTypeURI

  data IndividualURI : Set where
    JackURI : IndividualURI
    JillURI : IndividualURI    

  data Literal : Set where
    natLit : ℕ → Literal
    
  data Δᴰ : Set where
    natural : ℕ → Δᴰ
    string : String → Δᴰ

  data Δᴵ : Set where
    C : ClassURI → Δᴵ
    DP : DataPropertyURI → Δᴵ    
    OP : ObjectPropertyURI → Δᴵ
    I : IndividualURI → Δᴵ

  _ᶜ : ClassURI → Pred Δᴵ lzero
  _ᶜ OwlThing x = ⊤
  _ᶜ OwlNothing x = ⊥
  _ᶜ AgentURI (C OwlThing) = ⊥
  _ᶜ AgentURI (C OwlNothing) = ⊤
  _ᶜ AgentURI (C AgentURI) = ⊤
  _ᶜ AgentURI (C PersonURI) = ⊤
  _ᶜ AgentURI (DP x) = ⊥
  _ᶜ AgentURI (OP x) = ⊥
  _ᶜ AgentURI (I JackURI) = ⊤
  _ᶜ AgentURI (I JillURI) = ⊤
  _ᶜ PersonURI (C OwlThing) = ⊥
  _ᶜ PersonURI (C OwlNothing) = ⊤
  _ᶜ PersonURI (C AgentURI) = ⊥
  _ᶜ PersonURI (C PersonURI) = ⊤
  _ᶜ PersonURI (DP x) = ⊥
  _ᶜ PersonURI (OP x) = ⊥
  _ᶜ PersonURI (I JackURI) = ⊤
  _ᶜ PersonURI (I JillURI) = ⊤
  
  _ᴰᵀ : DataTypeURI → Pred Δᴰ lzero
  _ᴰᵀ StringURI (string x) = ⊤
  _ᴰᵀ StringURI (natural n) = ⊥

  _ᴸᵀ : Literal → Δᴰ
  natLit x ᴸᵀ = natural x

  _ᴰᴾ : DataPropertyURI → Pred (Δᴵ × Δᴰ) lzero
  _ᴰᴾ OwlTopDataProperty y = ⊤
  _ᴰᴾ OwlBottomDataProperty y = ⊥
  _ᴰᴾ NameURI (C x , proj₂) = ⊥
  _ᴰᴾ NameURI (DP OwlTopDataProperty , proj₂) = ⊥ 
  _ᴰᴾ NameURI (DP OwlBottomDataProperty , proj₂) = ⊤
  _ᴰᴾ NameURI (DP NameURI , natural x) = ⊥
  _ᴰᴾ NameURI (DP NameURI , string x) = ⊤
  _ᴰᴾ NameURI (OP x , proj₂) = ⊥
  _ᴰᴾ NameURI (I x , proj₂) = ⊥
  
  _ᴼᴾ : ObjectPropertyURI → Pred (Δᴵ × Δᴵ ) lzero
  _ᴼᴾ OwlTopObjectProperty y = ⊤
  _ᴼᴾ OwlBottomObjectProperty y = ⊥
  _ᴼᴾ KnowsURI (C x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (DP x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (OP x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (I JackURI , C x) = ⊥
  _ᴼᴾ KnowsURI (I JackURI , DP x) = ⊥
  _ᴼᴾ KnowsURI (I JackURI , OP x) = ⊥
  _ᴼᴾ KnowsURI (I JackURI , I JackURI) = ⊤
  _ᴼᴾ KnowsURI (I JackURI , I JillURI) = ⊤
  _ᴼᴾ KnowsURI (I JillURI , C x) = ⊥
  _ᴼᴾ KnowsURI (I JillURI , DP x) = ⊥
  _ᴼᴾ KnowsURI (I JillURI , OP x) = ⊥
  _ᴼᴾ KnowsURI (I JillURI , I JackURI) = ⊤
  _ᴼᴾ KnowsURI (I JillURI , I JillURI) = ⊤

  open import Facet
  _ᶠᴬ : Facet × Literal → Pred Δᴰ lzero
  _ᶠᴬ x y = ⊥
  
  _ᴵ : IndividualURI → Δᴵ
  x ᴵ = I x

  open import OWL
         ClassURI 
         IndividualURI
         DataTypeURI
         DataPropertyURI
         ObjectPropertyURI
         Literal
         Δᴵ
         Δᴰ
         _ᶜ
         _ᴰᵀ
         _ᴸᵀ 
         _ᴵ
         _ᴰᴾ
         _ᴼᴾ
         _ᶠᴬ
         OwlThing
         OwlNothing
         refl
         refl
         OwlTopObjectProperty
         OwlBottomObjectProperty
         refl
         refl
         OwlTopDataProperty
         OwlBottomDataProperty
         refl
         refl
         (λ _ → zero)
         (λ _ → zero)
  
  
  myTheory : Theory _
  myTheory = ClassRule (SubClassOf (OwlClassURI (OC AgentURI))
                                   (OwlClassURI (OC OwlThing))) ∷
             ClassRule (SubClassOf (OwlClassURI (OC PersonURI))
                                   (OwlClassURI (OC AgentURI))) ∷
             ObjectPropertyRule (ObjectPropertyRange (OP KnowsURI)
                                                     (OwlClassURI (OC AgentURI))) ∷
             ObjectPropertyRule (ObjectPropertyDomain (OP KnowsURI)
                                                      (OwlClassURI (OC AgentURI))) ∷ []

  testMyTheory : ∣ myTheory ∣
  testMyTheory = (λ x₁ → tt) ,
                 ((λ {x} p → personIsAgent x p) ,
                   ((λ x y p → agentRange x y p) ,
                     ((λ x y p → agentDomain x y p) , tt)))
               where personIsAgent : ∀ x → x ∈ PersonURI ᶜ → x ∈ AgentURI ᶜ
                     personIsAgent (C OwlThing) ()
                     personIsAgent (C OwlNothing) p = tt
                     personIsAgent (C AgentURI) p = tt
                     personIsAgent (C PersonURI) p = tt
                     personIsAgent (DP x) () 
                     personIsAgent (OP x) ()
                     personIsAgent (I JackURI) p = tt
                     personIsAgent (I JillURI) p = tt
                     {- lack of simultaneously range and domain restrictions is irritating -}
                     agentRange : ∀ x y → (x , y) ∈ KnowsURI ᴼᴾ → y ∈ AgentURI ᶜ
                     agentRange (C x) y ()
                     agentRange (DP x) y ()
                     agentRange (OP x) y ()
                     agentRange (I JackURI) (C OwlThing) ()
                     agentRange (I JackURI) (C OwlNothing) p = tt
                     agentRange (I JackURI) (C AgentURI) p = tt
                     agentRange (I JackURI) (C PersonURI) p = tt
                     agentRange (I JillURI) (C OwlThing) ()
                     agentRange (I JillURI) (C OwlNothing) p = tt
                     agentRange (I JillURI) (C AgentURI) p = tt
                     agentRange (I JillURI) (C PersonURI) p = tt
                     agentRange (I JackURI) (DP x) ()
                     agentRange (I JillURI) (DP x) ()
                     agentRange (I JackURI) (OP x₁) ()
                     agentRange (I JillURI) (OP x₁) ()
                     agentRange (I x) (I JackURI) p = tt
                     agentRange (I x) (I JillURI) p = tt
                     {- more pattern matching in the interpretation function 
                        would easy our lives here... -}
                     agentDomain : ∀ x y → (x , y) ∈ KnowsURI ᴼᴾ → x ∈ AgentURI ᶜ
                     agentDomain (C OwlThing) (C x₁) ()
                     agentDomain (C OwlNothing) (C x₁) p = tt
                     agentDomain (C AgentURI) (C x₁) p = tt
                     agentDomain (C PersonURI) (C x₁) p = tt
                     agentDomain (DP x) (C x₁) ()
                     agentDomain (OP x) (C x₁) ()
                     agentDomain (I JackURI) (C x₁) p = tt
                     agentDomain (I JillURI) (C x₁) p = tt
                     agentDomain (C OwlThing) (DP x₁) ()
                     agentDomain (C OwlNothing) (DP x₁) ()
                     agentDomain (C AgentURI) (DP x₁) ()
                     agentDomain (C PersonURI) (DP x₁) ()
                     agentDomain (DP OwlTopDataProperty) (DP x₁) ()
                     agentDomain (DP OwlBottomDataProperty) (DP x₁) ()
                     agentDomain (DP NameURI) (DP OwlTopDataProperty) ()
                     agentDomain (DP NameURI) (DP OwlBottomDataProperty) ()
                     agentDomain (DP NameURI) (DP NameURI) ()
                     agentDomain (OP x) (DP x₁) ()
                     agentDomain (I JackURI) (DP x₁) p = tt
                     agentDomain (I JillURI) (DP x₁) p = tt
                     agentDomain (C OwlThing) (OP x₁) ()
                     agentDomain (C OwlNothing) (OP x₁) p = tt
                     agentDomain (C AgentURI) (OP x₁) p = tt
                     agentDomain (C PersonURI) (OP x₁) p = tt
                     agentDomain (DP x) (OP x₁) ()
                     agentDomain (OP x) (OP x₁) ()
                     agentDomain (I JackURI) (OP x₁) p = tt
                     agentDomain (I JillURI) (OP x₁) p = tt
                     agentDomain (C OwlThing) (I JackURI) ()
                     agentDomain (C OwlNothing) (I JackURI) p = tt
                     agentDomain (C AgentURI) (I JackURI) p = tt
                     agentDomain (C PersonURI) (I JackURI) p = tt
                     agentDomain (DP x) (I JackURI) ()
                     agentDomain (OP x) (I JackURI) ()
                     agentDomain (I JackURI) (I JackURI) p = tt
                     agentDomain (I JillURI) (I JackURI) p = tt
                     agentDomain (C OwlThing) (I JillURI) ()
                     agentDomain (C OwlNothing) (I JillURI) p = tt
                     agentDomain (C AgentURI) (I JillURI) p = tt
                     agentDomain (C PersonURI) (I JillURI) p = tt
                     agentDomain (DP x) (I JillURI) ()
                     agentDomain (OP x) (I JillURI) ()
                     agentDomain (I JackURI) (I JillURI) p = tt
                     agentDomain (I JillURI) (I JillURI) p = tt
