----------------------------- MODULE OnlineShoppingPlatform -----------------------------

\* IMPORTS 
EXTENDS
    Naturals,
    Integers,
    Sequences,
    TLC,
    FiniteSets


CONSTANTS
    Shoppers, \* Set of customers ~ RM (Resource Manager)
    Providers, \* Set of individual goods providers
    Products, \* Set of products (available / unavailable)


ASSUME
    Cardinality(Shoppers) > 0   /\
    Cardinality(Providers) > 0  /\
    Cardinality(Products) >= 0


\* **** Supporting methods ****
IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

\* ****************************

Customers == [Shoppers -> 1..300] \* The set of all arrays indexed by the elements of Shoppers indexed with values from interval denoted by ..

Commodities == [Products -> 1..100]


VARIABLES shopperState, availableProducts, customers, commodities, boughtProducts, commodity


\* Type Control Invariants

TCTypeOK == shopperState \in [Shoppers -> {"idle", "browsing", "selecting", "ordering", "shipped"}]

TCInint == /\ shopperState = [shopper \in Shoppers |-> "idle"]
           /\ customers \in Customers
           /\ commodities \in Commodities
           /\ availableProductsSet \in [Shoppers -> SUBSET DOMAIN commodities]
           /\ availableProducts = [shopper \in Shoppers |-> SetToSeq(availableProductsSet[shopper])]
           /\ availableProductsIndex = [shopper \in Shoppers |-> 1]
           /\ boughtProducts = [shopper \in Shoppers |-> {}]
           /\ commodity = [shopper \in Shoppers |-> 0]


\* Shopper is on the web page and selects its product(s)
ProductsBrowsing(shopper) == /\ shopperState[shopper] = "idle"
                             /\ shopperState' = [shopperState EXCEPT ![shopper] = "browsing"] \* All other shoppers keep their states
                    \* TODO: Add conditions that must be fulfilled so the shopper can browsing


\* Shopper tries to select the product (add to basket)
ProductSelection(shopper) == /\ shopperState[shopper] = "selecting"
                             /\ IF availableProductsIndex[self] <= Len(availableProducts[self])
                                THEN commodity' = [commodity EXCEPT ![shopper] = availableProducts[shopper]]
                             \* TODO: Add conditions that must be fulfilled so the shopper can select goods

\* Shopper procceds to the busket finalize the order
ProductOrdering(shopper) == /\ shopperState[shopper] = "ordering"
                            \* TODO: Add conditions that must be fulfilled so the shopper can proceed to order

\* Shopper ordered it product
ProductShipping(shopper) == /\ shopperState[shopper] = "shipped"
                            \* TODO: Add conditions that must be fulfilled so the shopper can finalize the order

\* Shopper does not do anything at all
NonActive(shopper) == /\ shopperState[shopper] = "idle"
                            \* TODO: Add conditions that must be fulfilled so the shopper can be non-active

\* State Automat formula of the Online Store
OnlineShopping(shopper) == /\ ProductsBrowsing(shopper)
                           \/ ProductSelection(shopper)
                           \/ ProductOrdering(shopper)
                           \/ ProductShipping(shopper)
                           \/ NonActive(shopper)

=========================================================================================