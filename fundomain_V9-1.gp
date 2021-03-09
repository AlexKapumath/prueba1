
/* Updated 2021, March 08 */
/********************************************************************************************************************************************/
/* The subject here is determine Shintani fundamental domains for non-totall complex number fields */
/* From the signed domains obtained by the works of Diaz y Diaz, Espinoza and Friedman (now implemented in archive "SignedFundlDomain_V2.gp")*/
/* The works of Diaz y Diaz, Espinoza and Friedman are:                                                   */
/* [DDF14] Diaz y Diaz and Friedman, "Signed fundamental domain for totally real number fields" (2014)  [MR4105945]    */
/* [EF20] Espinoza and Friedman, "Twisters and Signed fundamental domains of number fields" (2020)  [MR3198753]        */
/* Our implementation is also based in the description of rational cones by inequalities (or H-representation) and     */
/* generators (or R-representation). For this we use the work of Fukuda and Prodon:     */
/* [FP96] Fukuda and Prodon, "Double description method revisited" (1996)  [MR1448924]  */
  
/*---------------------- Global variables ------*/
\\HV.rays=HV[1];
\\HV.ineqs=HV[2];

\p 600  \\ realprecision = 616 significant digits (600 digits displayed).
/********************************************************************************************************************************************/
/*****************************************************************************/
/*                                                                           */
/*    (Main) Algorithm to determine fundamental domains for number fields    */
/*                  from a signed one.                                       */
/*                                                                           */
/*****************************************************************************/
/* Given "p" a irreducible polynomial over Q, which define a number field K=bnfinit(p)=Q(theta) */

/*** INPUT: W=[p,U]; where p=K.pol; U=topu(K) generator of the group of the totally positive units (see function "topu()" below)  */
/*** For the generator e_1,...,e_r of the group U, where r=r1+r2-1 (rank of U). */
/*** The finite set : expn=lista(r,l) represent the r-tuples of the exponents of units in U (see function "lista()" below) */
/*** That is, for each [a_1,...,a_r] (a_j integers) we have that the product (e_1)^(a_1)*....(e_r)^(a_r) belongs to U */
/*** and l is a natural number fixed such that the sum |a_1|+...+|a_r| is less than or equal to l.*/

/*** OUTPUT: [G,D,t1] data of a possible true fundamental domain for K */
/*** where G=[p,K.disc,U,[a,b], [a1,b1], V, S, #S, #expn] */
/*** [a,b]=[#Initial of Negative Cones,#Initial of Positive Cones */
/*** In all process, we only consider n-dimensional cones ignoring lower-dimensional cones (n=[K:Q] its extension degree)*/
/*** [a1,b1]=[#Final of Negative Cones after remove some cones,#Final of Positive Cones after remove some cones] */
/*** IF a1=0, then we have "b1" n-dimensional rational polyhedral cones as a TRUE fundamental domain together with some proper faces*/
/*** V=expn if a1!=0, otherwise V=[] */
/*** S subset of "expn" of units used to remove the common intersection between interiors of negative and positive cones */
/*** D=[G,[N0,P0],[N1,P1]] */
/*** where N0=list initial of negative cones and P0=list initial of positive cones */
/*** N1=list obtained of negative cones after of use units in V */
/*** P1=list obtained of positive cones after of use units in V */
/*** If N1=[](empty) then the cones in P1 form a true fundamental domain */
/*** Each cone in P1 is of the form [[R-repres., H-repres.],w], w=vector of signs +1 or -1 indicating the facets to add at each cone */ 
/*** t1=getwalltime()....t1=getwalltime()-t1 */

fudom(W,expn)=  
{my(p,U,d,r,S,L,t1,t2,P0,N0,P,N,P1,N1,G,D,a,b,a1,b1,V,u,c,c1,h1,h2); 
print1("Using method: Weight -->Lexic.");
[p,U]=W;    
r=#U;     \\ rank of U+, r=d.r1+d.r2-1;
t2=getwalltime();  
d=bnfinit(p);  \\ data of the number field
if(d.r2>0,L=signedfd2(U,d),L=signedfd1(U,d));  \\Signed fund'l domain obtained by the algorithm given in "SignedFundlDomain_V2.gp".
t2=getwalltime()-t2;
a=#L[1];         \\ initial number of n-dimensional negative cones.
b=#L[2];         \\ initial number of n-dimensional positive cones.
t1=getwalltime();  
P0=vector(b,i,HV(L[2][i],d)); \\ list of cones as [generators, inequalities]=[R-repres., H-repres.]
if(a==0,         \\ means that such signed domain is a true one.
    P0=ABoundary(P0,d);         \\ Adding the facets in each cone to obtain a true fundamental domain.
    G=[p, d.disc, U, [0,b], [0,b], [], [], 0, #expn];    \\ S=[]=empty list (since we do not need using any unit to remove negative cones).
    D=[G,[[], P0],[[], P0]];
    );        
if(a>0,          \\ means that there is an n-dimensional NEGATIVE cone.
    S=[];     
    N0=vector(a,i,HV(L[1][i],d));         \\ list of cones as [R-repres, H-repres]
    N=vector(a,i,[N0[i], [N0[i]]]);       \\ Each cone is considered as [Cone=C, List of subcones asociated to C]
    P=vector(b,i,[P0[i], [P0[i]]]);   
    V=expn;            \\ Order of units with method: Weight -->Lexic. (see "lista()" below)
    for(j=1,#V,
        u=lift(Mod(prod(i=1,r,U[i]^(V[j][i])),p));   
        [N,P,h1,h2]=SeplistCs(N,P,u,d);                    \\ separation of (lists of) cones by the unit u.        
        if(h1!=0, S=concat(S,[concat([V[j]],h1)]);print1(". "j"-th unit is used"), print1(". "j"-th unit is not used") );
                  \\ h1!=0 (there exists some intersection in a some pair of cones), so the unit V[j] is used.
        c=[length(l[2]) | l<-N, length(l[2])!=0];           \\ length of each non-empty list of negative cones 
        print1(". Remain remove " length(c) "--(" vecsum(c) " cones) lists of " a " lists of negative cones. ");
        c1=[length(l[2]) | l<-P, length(l[2])!=0];                 \\ length of each non-empty list of positive cones 
        print1(". Remain " length(c1) "--(" vecsum(c1) " cones) lists of " b " lists of positive cones. ");
        if(length(c)==0, break());                          \\ if #c=0 means the interior of negatives cones have been deleting.
      );
    a1=vecsum([length(l[2]) | l<-N, length(l[2])!=0]);   \\ a1 could be different to 0 if there is another unit does not considered in "V".
    b1=vecsum([length(l[2]) | l<-P, length(l[2])!=0]);   \\ number of positive cones obtained.
    G=[p, d.disc, U, [a,b], [a1,b1], V, S, #S, #expn];   \\ S in the set of units used in all the proccess; l=#expn.
    N1=[]; for(j=1,a, N1=concat(N1,N[j][2])); 
    P1=[]; for(j=1,b, P1=concat(P1,P[j][2])); 
    P1=ABoundary(P1,d);      \\ Adding which facets of each cone to obtain a true fundamental domain.
    D=[G,[N0,P0],[N1,P1]];   \\ if in N1 is empty (i.e. N1 has not negative cones) then P1 is a true fundamental domain (with some boundaries)
    );
t1=getwalltime()-t1;
return([G,D,t1,t2]); 
}









