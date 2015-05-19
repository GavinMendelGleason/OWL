
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Vec hiding (_∈_)
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)
open import Relation.Binary.Core
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.String renaming (_≟_ to _≟s_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

module Example where

  data ClassURI : Set where
    OwlThing : ClassURI
    OwlNothing : ClassURI
    AgentURI : ClassURI
    PersonURI : ClassURI 

  --Class URI = Fin 4


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
  _ᶜ AgentURI (C x) = ⊥
  _ᶜ AgentURI (DP x) = ⊥
  _ᶜ AgentURI (OP x) = ⊥
  _ᶜ AgentURI (I JackURI) = ⊤
  _ᶜ AgentURI (I JillURI) = ⊤
  _ᶜ PersonURI (C x) = ⊥
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
  _ᴰᴾ NameURI (DP x , proj₂) = ⊥
  _ᴰᴾ NameURI (OP x , proj₂) = ⊥
  _ᴰᴾ NameURI (I JackURI , natural x) = ⊥
  _ᴰᴾ NameURI (I JackURI , string x) with x ≟s "Jack"
  _ᴰᴾ NameURI (I JackURI , string x) | yes p = ⊤
  _ᴰᴾ NameURI (I JackURI , string x) | no ¬p = ⊥
  _ᴰᴾ NameURI (I JillURI , natural x) = ⊥
  _ᴰᴾ NameURI (I JillURI , string x) with x ≟s "Jill"
  _ᴰᴾ NameURI (I JillURI , string x) | yes p = ⊤
  _ᴰᴾ NameURI (I JillURI , string x) | no p = ⊥
  
  _ᴼᴾ : ObjectPropertyURI → Pred (Δᴵ × Δᴵ ) lzero
  _ᴼᴾ OwlTopObjectProperty y = ⊤
  _ᴼᴾ OwlBottomObjectProperty y = ⊥
  _ᴼᴾ KnowsURI (C x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (DP x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (OP x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (I x , C y) = ⊥
  _ᴼᴾ KnowsURI (I x , DP y) = ⊥
  _ᴼᴾ KnowsURI (I x , OP y) = ⊥
  _ᴼᴾ KnowsURI (I x , I y) with x | y
  _ᴼᴾ KnowsURI (I x , I y) | JackURI | JackURI = ⊤
  _ᴼᴾ KnowsURI (I x , I y) | JackURI | JillURI = ⊤
  _ᴼᴾ KnowsURI (I x , I y) | JillURI | JackURI = ⊤
  _ᴼᴾ KnowsURI (I x , I y) | JillURI | JillURI = ⊤

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
                     personIsAgent (C x) ()
                     personIsAgent (DP x) () 
                     personIsAgent (OP x) ()
                     personIsAgent (I JackURI) p = tt
                     personIsAgent (I JillURI) p = tt
                     {- lack of simultaneously range and domain restrictions is irritating -}
                     agentRange : ∀ x y → (x , y) ∈ KnowsURI ᴼᴾ → y ∈ AgentURI ᶜ
                     agentRange (C x) (C x₁) ()
                     agentRange (C x) (DP x₁) ()
                     agentRange (C x) (OP x₁) ()
                     agentRange (C x) (I x₁) ()
                     agentRange (DP x) (C x₁) ()
                     agentRange (DP x) (DP x₁) ()
                     agentRange (DP x) (OP x₁) ()
                     agentRange (DP x) (I x₁) ()
                     agentRange (OP x) (C x₁) ()
                     agentRange (OP x) (DP x₁) ()
                     agentRange (OP x) (OP x₁) ()
                     agentRange (OP x) (I x₁) ()
                     agentRange (I x)  (C x₁) ()
                     agentRange (I x) (OP x₁) ()
                     agentRange (I x) (DP x₁) ()
                     agentRange (I x) (I x₁) x₂ with x | x₁
                     agentRange (I x) (I x₁) x₂ | JackURI | JackURI = tt
                     agentRange (I x) (I x₁) x₂ | JackURI | JillURI = tt
                     agentRange (I x) (I x₁) x₂ | JillURI | JackURI = tt
                     agentRange (I x) (I x₁) x₂ | JillURI | JillURI = tt 
                     {- more pattern matching in the interpretation function 
                        would easy our lives here... -}
                     agentDomain : ∀ x y → (x , y) ∈ KnowsURI ᴼᴾ → x ∈ AgentURI ᶜ
                     agentDomain (C x) y ()
                     agentDomain (DP x) y ()
                     agentDomain (OP x) y ()
                     agentDomain (I x) (C x₁) ()
                     agentDomain (I x) (DP x₁) ()
                     agentDomain (I x) (OP x₁) ()
                     agentDomain (I JackURI) (I y) p = tt
                     agentDomain (I JillURI) (I y) p = tt

