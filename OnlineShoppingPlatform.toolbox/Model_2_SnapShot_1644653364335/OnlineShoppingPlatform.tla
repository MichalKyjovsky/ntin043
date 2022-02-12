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
    Products \* Set of products (available / unavailable)


ASSUME
    Cardinality(Shoppers) > 0   /\
    Cardinality(Products) >= 0


\* **** Supporting methods ****
IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

\* ****************************

Customers == [Shoppers -> 1..5] \* The set of all arrays indexed by the elements of Shoppers indexed with values from interval denoted by ..

Commodities == [Products -> 1..2]


VARIABLES shopperState, availableProducts, customers, commodities, boughtProducts, commodity, availableProductsSet, availableProductsIndex, bought

vars == << shopperState, availableProducts, customers, commodities, boughtProducts, commodity, availableProductsSet, availableProductsIndex, bought >>

\* Type Control Invariants

TCTypeOK == shopperState \in [Shoppers -> {"idle", "browsing", "selecting", "ordering", "shipped", "served"}]

            \* Global variables
TCInint == /\ (shopperState = [shopper \in Shoppers |-> "browsing"])
           /\ customers \in Customers
           /\ commodities \in Commodities
           /\ bought = {}
            \* Variables for the states of actual shopping activities    
           /\ availableProductsSet \in [Shoppers -> SUBSET DOMAIN commodities]
           /\ availableProducts = [shopper \in Shoppers |-> SetToSeq(availableProductsSet[shopper])]
           /\ availableProductsIndex = [shopper \in Shoppers |-> 1]
           /\ boughtProducts = [shopper \in Shoppers |-> {}]
           /\ commodity = [shopper \in Shoppers |-> 0]


\* Shopper is on the web page and selects its product(s)
ProductsBrowsing(shopper) == /\ shopperState[shopper] = "browsing"
                             /\ shopperState' = [shopperState EXCEPT ![shopper] = "browsing"] \* All other shoppers keep their states
                             /\ UNCHANGED << customers, commodities, boughtProducts, availableProducts, availableProductsIndex, availableProductsSet >>


\* Shopper tries to select the product (add to basket)
ProductSelection(shopper) == /\ shopperState[shopper] = "selecting"
                             /\ IF availableProductsIndex[shopper] <= Len(availableProducts[shopper])
                                THEN /\ commodity' = [commodity EXCEPT ![shopper] = availableProducts[shopper][availableProductsIndex[shopper]]]
                                     /\ shopperState' = [shopperState EXCEPT ![shopper] = "ordering"]
                                ELSE /\ FALSE
                             /\ UNCHANGED << customers, commodities, boughtProducts, availableProducts, availableProductsIndex, availableProductsSet, bought >>

\* Shopper procceds to the busket finalize the order
ProductOrdering(shopper) == /\ shopperState[shopper] = "ordering"
                            /\ IF commodities[commodities[shopper]] <= customers[shopper]
                               THEN /\ customers' = [customers EXCEPT ![shopper] = customers[shopper] - commodities[commodity[shopper]]]
                                    /\ boughtProducts' = [boughtProducts EXCEPT ![shopper] = boughtProducts[shopper] \union {commodities[shopper]}]
                                    /\ bought' = (bought \union commodities[shopper])
                               ELSE /\ TRUE
                                    /\ UNCHANGED << customers, bought, boughtProducts >>
                            /\ shopperState' = [shopperState EXCEPT ![shopper] = "selecting"]
                            /\ UNCHANGED << commodities, availableProducts, availableProductsIndex, availableProductsSet, commodity >>

\* Shopper ordered product and specifies shippment
ProductShipping(shopper) == /\ shopperState[shopper] = "shipping"
                            /\ shopperState' = [shopperState EXCEPT ![shopper] = "served"]
                            /\ UNCHANGED << availableProducts, customers, commodities, boughtProducts, commodity, availableProductsSet, availableProductsIndex, bought >>


\* Shopper does not do anything at all
NonActive(shopper) == /\ shopperState[shopper] = "idle"
                      /\ (shopperState' = [shopperState EXCEPT ![shopper] = "served"] \/ shopperState' = [shopperState EXCEPT ![shopper] = "browsing"])
                      /\ UNCHANGED << availableProducts, customers, commodities, boughtProducts, commodity, availableProductsSet, availableProductsIndex, bought >>

\* State Automat formula of the Online Store
OnlineShopping(shopper) == /\ ProductsBrowsing(shopper)
                           \/ ProductSelection(shopper)
                           \/ ProductOrdering(shopper)
                           \/ ProductShipping(shopper)


\* TERMINATION ASSERTIONS

Terminating == /\ (\A shopper \in Shoppers: shopperState[shopper] = "served") 
               /\ UNCHANGED vars
               
Next == (\E shopper \in Shoppers: OnlineShopping(shopper))
        \/ Terminating
        
Spec == TCInint /\ [][Next]_vars

Termination == <>(\A shopper \in Shoppers: shopperState[shopper] = "served")

=========================================================================================