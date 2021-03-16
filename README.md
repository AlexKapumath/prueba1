# Computing of Shintani fundamental domains
Here we give an algorithm (in Pari/GP) to obtain a TRUE fundamental domain from a SIGNED fundamental domain for the action of the totally positive units group of a non-totally complex number field. Such signed domains were established in the works of Diaz y Diaz, Espinoza and Friedman:

[DDF14] Diaz y Diaz and Friedman, "Signed fundamental domain for totally real number fields" (2014)  [MR4105945]    
[EF20] Espinoza and Friedman, "Twisters and Signed fundamental domains of number fields" (2020)  [MR3198753]        

 Our implementation is also based in the description of rational cones by inequalities (or H-representation) and    
 generators (or V-representation). For this we use the work of Fukuda and Prodon:   
 
 [FP96] Fukuda and Prodon, "Double description method revisited" (1996)  [MR1448924]  

In archive "SignedFundlDomain_V2.gp" we implement the signed domains given in [DDF14] (for totally real fields) [EF20] (for all the non-totally complex fields).
  
For example: (in Pari/GP)

? p=x^4 - 5*x^2 + 3;

? K=bnfinit(p); \\ data of Pari/GP

? U=topu(K)    \\ generators of the totally positives unit group of K  

U=[x^2 + 2*x + 1, x^2 - 2*x + 1, -x^3 + 2*x^2 + x - 1]

?




