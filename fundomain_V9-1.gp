
/* Updated 2021, March 14 */
/********************************************************************************************************************************************/
/* The subject here is determine Shintani fundamental domains for non-totall complex number fields */
/* from the signed domains obtained by the works of Diaz y Diaz, Espinoza and Friedman (now implemented in "SignedFundlDomain_V2.gp")*/
/* The works of Diaz y Diaz, Espinoza and Friedman are:                                                   */
/* [DDF14] Diaz y Diaz and Friedman, "Signed fundamental domain for totally real number fields" (2014)  [MR4105945]    */
/* [EF20] Espinoza and Friedman, "Twisters and Signed fundamental domains of number fields" (2020)  [MR3198753]        */
/* Our implementation is also based in the description of rational cones by inequalities (or H-representation) and     */
/* generators (or R- or V-representation). For this we use the work of Fukuda and Prodon:     */
/* [FP96] Fukuda and Prodon, "Double description method revisited" (1996)  [MR1448924]  */
  

/*---------------------- Global variables ------*/
fudom.data=fudom[1]; \\ this is [p, K.disc, U, [a,b], [a1,b1], S, #S] given in the function "fudom()"
fudom.truefund=fudom[2][2][2];  \\ this is the list of full-dimensional rational cones that defines a TRUE fundl domain 
fudom.ngcones=fudom[2][1][1]; \\ negative cones initial given by algorithm in "SignedFundlDomain_V2.gp"
fudom.pscones=fudom[2][1][2]; \\ positive cones initial
fudom.timetruefd=fudom[3];    \\ time in miliseconds to obtain a true fundamental domain from a signed one given
fudom.timesignedfd=fudom[4];  \\ time in miliseconds to obtain a signed fundamental domain
#
allocatemem(10^9);
\p 600     \\ realprecision = 616 significant digits (600 digits displayed).


/********************************************************************************************************************************************/
/*****************************************************************************/
/*                                                                           */
/*    (Main) Algorithm to determine a fundamental domain from a signed one   */
/*                  for a number field given.                                */
/*                                                                           */
/*****************************************************************************/
/*** Given "p" a irreducible polynomial over Q, which define a number field K=bnfinit(p)=Q(theta) */
/*** For the generator e_1,...,e_r of the group U of totally positive units, where r=r1+r2-1 (rank of U). */
/*** The finite set : V=lista(r,l) considered in this algorithm below represent the r-tuples of the exponents of units in U */
/*** That is, for each [a_1,...,a_r] (a_j integers) we have that the product (e_1)^(a_1)*....(e_r)^(a_r) belongs to U */
/*** and l is a natural number fixed such that the sum |a_1|+...+|a_r| is less than or equal to l.*/
/*** Here we only considere "l=5" which is sufficient to fields of degree less than or equal to 7, probably we need to take a value more greater than 5 for fields of degree >7, this also depends of number of negatives cones in a SIGNED fundamental domain.*/

/*** INPUT: W=[p,U]; where p=K.pol; U=topu(K) generator of the group of the totally positive units (see function "topu()" below)  */

/*** OUTPUT: [G,D,t1,t2] data of a possible true fundamental domain for K */
/*** where G=[p, K.disc, U, [a,b], [a1,b1], S, #S] */
/*** [a,b]=[#Initial of Negative Cones, #Initial of Positive Cones] */
/*** In all process, we only consider n-dimensional cones ignoring lower-dimensional cones (n=[K:Q] its extension degree)*/
/*** [a1,b1]=[#Final of Negative Cones after remove some cones,#Final of Positive Cones after remove some cones] */
/*** IF a1=0, then we have "b1" n-dimensional rational polyhedral cones as a TRUE fundamental domain together with some proper faces*/
/*** S subset of "lista(r,5)" of units used to remove the common intersection between interiors of negative and positive cones */
/*** D=[[N0,P0],[N1,P1]] */
/*** where N0=list initial of negative cones and P0=list initial of positive cones */
/*** N1=list obtained of negative cones after of use units in lista(r,5) */
/*** P1=list obtained of positive cones after of use units in lista(r,5) */
/*** If N1=[](empty) then the cones in P1 form a TRUE fundamental domain */
/*** Each cone in P1 is given in the form [[V-repres., H-repres.],w], where w=vector of signs +1 or -1 (see "ABoundary()" below) */ 
/*** t1=time im miliseconds to obtain a true fundamental domain given a signed one*/
/*** t2=time im miliseconds to obtain a signed fundamental domain */

fudom(W)=  
{my(p,U,d,r,S,L,t1,t2,P0,N0,P,N,P1,N1,G,D,a,b,a1,b1,V,u,c,c1,h1,h2); 
print1("Using method: Weight -->Lexic.");
[p,U]=W;    
r=#U;            \\ rank of U+, r=d.r1+d.r2-1;
t2=getwalltime();  
d=bnfinit(p);    \\ data of the number field K obtained by Pari/gp
if(d.r2>0,L=signedfd2(U,d),L=signedfd1(U,d));  \\Signed fund'l domain obtained by the algorithm given in "SignedFundlDomain_V2.gp"
t2=getwalltime()-t2;
a=#L[1];         \\ initial number of n-dimensional negative cones.
b=#L[2];         \\ initial number of n-dimensional positive cones.
V=lista(r,5);      \\ the elements are ordered by "weight" and "lexicographically", see function "lista()" below 
t1=getwalltime();  
P0=vector(b,i,HV(L[2][i],d)); \\ list of cones as [generators, inequalities]=[V-repres., H-repres.]
if(a==0,         \\ means that such signed domain is a true one.
    P0=ABoundary(P0,d);         \\ Adding the facets in each cone to obtain a true fundamental domain.
    G=[p, d.disc, U, [0,b], [0,b], [], 0];    \\ S=[]=empty list (since we do not need using any unit to remove negative cones).
    D=[L,[[], P0]];
    );        
if(a>0,                    \\ means that there is an n-dimensional NEGATIVE cone.
    S=[];     
    N0=vector(a,i,HV(L[1][i],d));         \\ list of cones as [V-repres, H-repres]
    N=vector(a,i,[N0[i], [N0[i]]]);       \\ Each cone is considered as [Cone=C, List of subcones asociated to C]
    P=vector(b,i,[P0[i], [P0[i]]]);   
    for(j=1,#V,
        u=lift(Mod(prod(i=1,r,U[i]^(V[j][i])),p));   
        [N,P,h1,h2]=SeplistCs(N,P,u,d);                    \\ separation of (lists of) cones by the unit u.        
        if(h1!=0, S=concat(S,[concat([V[j]],h1)]);print1(". "j"-th unit is used"), print1(". "j"-th unit is not used") );
                       \\ h1!=0 (there exists some intersection in a some pair of cones), so the unit V[j] is used.
        c=[length(l[2]) | l<-N, length(l[2])!=0];           \\ length of each non-empty list of negative cones 
        print1(". Remain remove " length(c) "--(" vecsum(c) " cones) lists of " a " lists of negative cones. ");
        c1=[length(l[2]) | l<-P, length(l[2])!=0];                 \\ length of each non-empty list of positive cones 
        print1(" Remain " length(c1) "--(" vecsum(c1) " cones) lists of " b " lists of positive cones. ");
        if(length(c)==0, break());                          \\ if #c=0 means the interior of negatives cones have been deleting.
      );
    a1=vecsum([length(l[2]) | l<-N, length(l[2])!=0]);   \\ a1 could be different to 0 if there is another unit does not considered in "V".
    b1=vecsum([length(l[2]) | l<-P, length(l[2])!=0]);   \\ number of positive cones obtained.
    G=[p, d.disc, U, [a,b], [a1,b1], S, #S];   \\ S in the set of units used in all the proccess; l=#expn.
    N1=[]; for(j=1,a, N1=concat(N1,N[j][2])); 
    P1=[]; for(j=1,b, P1=concat(P1,P[j][2])); 
    P1=ABoundary(P1,d);    \\ Adding which facets of each cone to obtain a true fundamental domain.
    D=[L,[N1,P1]];         \\ if in N1 is empty (i.e. N1 has not negative cones) then P1 is a true fundamental domain (with some boundaries)
    );
if(G[5][1]==0,print1(" A true fund'l domain have been obtained with " G[5][2] " " d.r1+2*d.r2"-dimensional cones."), warning("the domain obtained is still signed, you need to change the function lista(r,5) by lista(r,l) taking some l>5."));
t1=getwalltime()-t1;
return([G,D,t1,t2]); 
}



/********************************************************************************************************************************************/
/*****************************************************************************/
/*                                                                           */
/*    Algorithm to obtain fundamental domains from a signed one              */
/*                  for a LIST number fields given.                          */
/*                                                                           */
/*****************************************************************************/
/* Given a list of irreducible polynomials "p" of degree n (fixed), so for each "p" defines a number field K=bnfinit(p)=Q(theta) */

/*** INPUT: A list "v" whose elements are of the form [irredu. polynomial p degree n, generators of the totally positive units group in K] */ 
/*** In this routine we consider a limit time on seconds ("sec") to obtain a possible TRUE fundamental domain in each number field */

/*** OUTPUT: Write an archive with a data for each (possible) fundamental domain of each number field in the form: */
/*** for each number field we determine a tuple [G,t1,t2] */  
/*** G=[p,d.disc,U,[#N0,#P0],[#N1,#P1],S,#S] */
/*** where G were descrited above. */


fundaldomains(v,sec)=
{\\my(F,G,D,v,t,t1,V);
write(Bfields1,"\\\\ Here we have a list [number fields,[fundamental units]] such that has NOT obtained its fundamental domain after of ", sec , " seconds.");
write(Bfields1,"");
write(timeFDs1, "\\\\ Each vector below is of the form:");
write(timeFDs1, "\\\\ [j,[p,d.disc,U,[#N0,#P0],[#N1,#P1],S,#S],t1,t2], where");
write(timeFDs1, "\\\\ p=irreduc. polynomial given; d.disc=discriminant of K; U=generators of the totally positive units group;");
write(timeFDs1, "\\\\ [#N0,#P0]=[#negative cones initial,#positive cones initial];");
write(timeFDs1, "\\\\ [#N1,#P1]=[#negative cones obtained,#positive cones obtained];");
write(timeFDs1, "\\\\ S subset of "lista(r,5)" of units used to remove the common intersection between interiors of negative and positive cones; S=[] if #N1==0 which implies that such signed domain is a true one;");
write(timeFDs1, "\\\\ #S=order of S;");
write(timeFDs1, "\\\\ j=position on the list given; t1=time on milseconds to obtain true fundl domain.");
write(timeFDs1, "\\\\ t2=time on milseconds to obtain a SIGNED fund'l domain established in SignedFundlDomain_V2.gp");
write(timeFDs1, "");
write(timeFDs1, "\\\\ Each fundamental domain is obtained in at most ", sec, " seconds.");
write(timeFDs1, "");
write(timeFDs1, "\\\\ Here we use the method-1: Weight ---> Lexicographic to order the units, see  function lista(r,l).");
write(timeFDs1, "");
ell=0; ell1=0;
for(j=1,#v,
   tiem1=getwalltime();
   Fund=alarm(sec,fudom(v[j]));
   if(type(Fund)=="t_ERROR",  write(Bfields1,"",v[j],"");ell=ell+1 , 
      [Gru,Dom,tim,tim0]=Fund;
      write(timeFDs1,"",[j,Gru,tim,tim0],""); ell1=ell1+1;
     );
   print1([[j],getwalltime()-tiem1]); 
 );
write(Bfields1, "");
write(Bfields1, "\\\\ For ", ell, " number fields such a TRUE domain has not been obtained.");
write(timeFDs1, "");
write(timeFDs1, "\\\\ A true domain has been obtained for ", ell1," number fields.");
}




/*****************************************************************************************************************************/
/*** Now we describe all the functions mentioned in the algorithm "fudom()" above ***/
/*****************************************************************************************************************************/
/*******************************************************************************************/
/*                                                                                         */
/*  1. Calculate of generator of the totally positive units group of a number field        */
/*                 (code established in the Manual Pari/gp)                                */
/*                                                                                         */
/*******************************************************************************************/

/* exponents of totally positive units generators on bnf.tufu */

tpuexpo(bnf)=
{my(K, S = bnfsignunit(bnf), [m,n] = matsize(S)); \\ m = bnf.r1, n = r1+r2-1
S = matrix(m,n, i,j, if (S[i,j] < 0, 1,0));
S = concat(vectorv(m,i,1), S); \\ add sign(-1)
K = matker(S * Mod(1,2));
if (K, mathnfmodid(lift(K), 2), 2*matid(n+1));
}


/* totally positive fundamental units (with a representation on integral basis) */
/*** INPUT: bnf=bnfinit(p) */
/*** OUTPUT: Totally positive fund'l units with representation on its integral basis */ 

tpu(bnf)=
{ my(ex = tpuexpo(bnf)[,2..-1]); \\ remove ex[,1], corresponds to 1 or -1
vector(#ex, i, nffactorback(bnf, bnf.tufu, ex[,i]));
}

/*totally positive fundamental units*/
/*** INPUT: bnf=bnfinit(p) */
/*** OUTPUT: U= totally positive fund'l units with representation in k_+ */
 
topu(bnf)=
{my(T,nf,U);
T=tpu(bnf);
nf=bnf.nf;
U=vector(#T,i,lift(nfbasistoalg(nf,T[i])));
return(U);
}


/*******************************************************************************************************************/
/********* LIST OF EXPONENT TO UNITS *********************************/
/* We consider the exponents of units group until an exponent given*/

/*** INPUT: two natural numbers r (=rank(U+)); l=is a natural number fixed)               */

/*** OUTPUT: L=lista(r,l) is a collection of vectors in R^{r} whose entries are integer numbers between -l and l */ 
/*** The finite set obtained L represent the r-tuples of the exponents of units in U    */
/*** I.e., For each element in L is of the form: */
/***       [a_1,...,a_r] (a_j integers) which represent the exponents of the product (e_1)^(a_1)*....(e_r)^(a_r) in U */
/***       and moreover, the sum |a_1|+...+|a_r| is less than or equal to l.*/
/*** All r-tuples in L are first ordered by its weight "|a_1|+...+|a_r|" and then lexicographically ordered those of the same weight, */
/*** such order we shall call "Weight -->Lexic."  */

lista(r,l)= 
{my(L,P,Q);
P=genn(r,l);
L=[vector(r,j)];
for(j=1,l,
   Q=[v| v<-P, vecsum(abs(v))==j]; \\ using the norm L1
   Q=vecsort(Q); L=concat(L,Q);
   );
return(L);   
}

genn(r,l)= \\ l represent the l-th iteration 
{my(S,P,Q);
if(l==0,P=[vector(r,i)]);
if(l>=1,
   S=[i|i<-[-l..l]]; \\ numbers between -l and l.
   P=[[S[i]]| i<-[1..#S]]; \\ initial step
   while(#P!=(#S)^r, P=concat(vector(#S,i,vector(#P,j,concat(P[j],[S[i]])))); next);
);
return(P);  
}


/***************************************************************************************************************************************/
/*****************************************************************************/
/*                                                                           */
/*    2. "HV" calculate an V-representation from its H-representation        */
/*         whose generators are in K_+ (and vice-versa by duality)           */
/*    (Here we use the method of Double Description Method "DDM")            */
/*              "BASED IN THE PAPER OF FUKUDA AND PRODON [FP96]"             */
/*****************************************************************************/
/* Given a number field K=bnfinit(polynomial)=Q(theta) */

/* This algorithm transforms an H-repr. into a V-repr. of a polyhedral cone if it is POINTED */
/* and conversely it also transforms a V-repre. into an H-repe. if the polyhedral cone is n-DIMENSIONAL */

/*** INPUT: v=[v_1,v_2...v_e] is a collection of elements in K (number field)    */
/*** which define an H-repres (respectively V-represen) of an n-dimensional pointed polyhedral cone P */
/*** d=bnfinit(polynomial) data given by Pari/gp */

/*** Recall that: v define a V-represen. for P, if P=C[v_1,v_2,...,v_e]:={sum_{j}t_jv_j: t_j=>0} */
/*** and v define an H-represen. for P, if P=H(L_1,...L_e):={x in X: L_j(x)=tr(v_jx) =>0} (intersection of half-spaces), X=R^(r1)*C^(r2) */


/*** OUTPUT: A pair [H-represen.,V-represen.(irredudant)] (respectively [V-represen.,H-repr.(irredundant)]) description for P */ 

HV(v,d)=  \\ v define an H-representation (respec. V-repren.) of an n-dimensional POINTED cone.
{my(w,S,L,R,t1,t0); 
w=check(v,d);     \\ taking a subset of n independent linear vectors on V_Q in the set v. (w subcollections of H-reprs.)
S=HV1(w,d);       \\ transformation of w on a V-repr.
L=[g|g<-v, vfind(w,g)==0];     \\these are the H-reprs. that we want add to the  cone w (or S)
for(j=1,#L,
    R=AddC([L[j],S,w],d);  \\ add H-repr. L[j] to the V-repr. initial S=HV1(T[1],d).
    [S,w]=R;
    );
return([w,S]);  \\ we note that if v is an H-repre (respec. V-repre) then S is V-repre (respec. H-repre) with S is irredundant ("By duality").
}


/**************************************************************************/
/* HV1 is to the case when the cone is a  "simplicial n-dimensional cone" */
/*** INPUT: S=simplicial cone (n=[k:Q])-dimensional with a V-represention (H-representation) whose generators are in K; d=bnfinit(poly) */

/*** OUTPUT: H= is an H-reprentation (V-representation) of the SIMPLICIAL n-dimensional cone S  */

HV1(S,d)=          
{my(nf,H,L,n,a);     
n=d.r1+2*d.r2;             \\n=[K:Q]
nf=d.nf; L=matrix(n,n, i,j, nfelttrace(nf,S[i]*S[j]));
H=matsolve(L,matid(n));   \\ inverse of the matrix L
H=Vec(H);
for(j=1,#H,
   a=vecsum(vector(n,i,Vec(H[j])[i]*S[i]));    \\ return a polymod which define the H-repr(V-repr) of S.
   H[j]=a/abs(content(a));
   );
return(H);         \\ when S is a V-repr.(H-repr.) of the cone then  H is an H-repr.(V-repr.) V ("By duality").
}



/*** INPUT: V is set of elements in K not necessarily independents, d=bnfinit(poly) */

/*** OUTPUT: E a subset (of V) of n independent elements over Q  */ 

check(V,d)= 
{my(nf,m,n,B,C,D,E);
m=#V;               \\ V is a set of m elements of K (m>=n).
n=d.r1+2*d.r2; nf=d.nf;
if(m>=n,
  B=vector(m,i,nfalgtobasis(nf,V[i])); B=mattranspose(Mat(B));
    if(matrank(B)==n,
        C=matindexrank(B); D=vecextract(B,C[1],C[2]); D=Vec(mattranspose(D)); E=vector(#D);
        for(j=1,#D, E[j]=lift(nfbasistoalg(nf,D[j])));
       );
  );
return(E);    \\ E is a subset of n vectors on v independent linear in V_Q. If E=0 then the set given have no "n" elements independent. 
}

ncheck(V,d)=
{my(nf,m,n,f,B);
m=#V;          \\ V is a set of m elements of K (m>=n).
n=d.r1+2*d.r2; nf=d.nf; f=0;
if(m>=n,B=vector(m,i,nfalgtobasis(nf,V[i])); B=Mat(B); 
  if(matrank(B)==n, f=1); 
  );
return(f); \\ f=1 means the set V contains n independent elements. f=0 otherwise.
}


/*Algorithm for verify when two (extreme) rays (v1,v2) in P(A) are neighbour or adjacent on P(A):=[w_1,...,w_m]:={x : tr(w_jx) >= 0} given*/
/*** INPUT: Given two rays v1 and v2 on a polyhedral cone P(A)=H-representation */ 
/*** T=[[v1,v2],P(A)] is a triple; d=bnfinit(k) */

/*** OUTPUT: return 1 if both rays generate a 2-dimensional face on the cone P(A), 0 otherwise */ 

nbour(T,d)=         
{my(nf,v1,v2,A,S,n,Z1,Z2,Z,B,C,f);
[v1,v2]=T[1]; A=T[2];     \\ all the elements of A be in K (warning!: here is necessary that P(A) be an H-representation)
S=[1..#A]; n=d.r1+2*d.r2; nf=d.nf;
Z1=[j|j<-S, nfelttrace(nf,A[j]*v1)==0]; \\ zone of zeros of ray v1
Z2=[j|j<-S, nfelttrace(nf,A[j]*v2)==0]; \\ zone of zeros of ray v2
Z=setintersect(Z1,Z2);    \\ because Z1 and Z2 are sets.
f=0;
if(#Z>=(n-2),          \\ If Z1 and Z2 are adjacent then Z has at least n-2 elements. 
   B=vecextract(A,Z);  \\ extracting the entries of vector A correspondiente to position on Z
   C=vector(#B,i,nfalgtobasis(nf,B[i])); C=Mat(C);
   if(matrank(C)==n-2, f=1);
  );
return(f);             \\f=1 means that the rays v1 and v2 are neighbour (or adjacent) on the polyhedral P(A).
}



/* Adding some restriction [w]: tr(wx) => 0, w\in k, of a pair (R;L) given , where L is an H-repr. and R thus V-repr. of L */
/*** INPUT: v=[w,R,L], where w is a inequality "tr(wx) => 0" and [R,L]=[V-representation,H-representation] is a cone given*/
/*** d= bnfinit(poly) */

/*** OUTPUT: return a new cone with this inequality added */ 

AddC(v,d)=         
{my(nf,w,R,L,Rp,Rn,R0,T,S,ray,e,f);
nf=d.nf;
[w,R,L]=v;
Rp=[r|r<-R, nfelttrace(nf,w*r)>0];   \\ set of positive rays on R respect to hyperplane "tr(wx)=0" generated by the restriction.
Rn=[r|r<-R, nfelttrace(nf,w*r)<0];   \\ similarly (negative rays)
R0=[r|r<-R, nfelttrace(nf,w*r)==0];  \\ similarly (zero rays)
T=[[a,b]|a<-Rp;b<-Rn];               \\ this is the set of pairs of rays positives and negatives respect to restriction "tr(wx)"
if(#T==0,S=[], T=[ad|ad<-T, nbour([ad,L],d)==1];  \\ here we consider only the adjacent pairs.
    S=vector(#T,j);
    for(j=1,#T, e=T[j][1]; f=T[j][2]; ray=nfelttrace(nf,w*e)*f-nfelttrace(nf,w*f)*e; S[j]=ray/abs(content(ray)));
  );
L=concat(L,[w]);
R=concat(concat(Rp,R0),S); \\ new V-representation of P after add the restriction w.
return([R,L]);   \\ new V-repr (without redundancies) and H-repr of the cone when we add the restriction w. (Here L could have some redudances)
}



/****************** Little routines which are used in other process***************************************/
/*** product of one collection of elements in K number field     */
/*** INPUT: A=list of elements in K                              */
/*** poli = is the irreducible polynomial that define to K */
/*** OUTPUT: B=the product of the elements of the list given A    */ 

prd(A,poli)=  
{my(B);
B=A[1];
for(j=2,#A,B=lift(Mod(B*A[j],poli))); 
return(B);
}

/*********/
/* multiplication of one element "u" on K on the cone given mod(polynomial) where the cone is given as V-repr and H-repr */
/*** INPUT: Given "u" in K */
/*** C=[C.generators,C.inequalities] */
/*** poli=polynomial defining the number field K */

/*** OUTPUT: return a new cone with this unit acting */ 

mulc(u,C,poli)=         
{my(A,B);
A=vector(#C[1],i,lift(Mod(u*C[1][i],poli)));       \\ multiplication of the unit u in the V-repr
A=vector(#A,i,A[i]/abs(content(A[i])));              \\ here we divide each entries by its abs(gcd(--)) > 0
B=vector(#C[2],i,lift(Mod(u^(-1)*C[2][i],poli)));  \\ multiplication of the unit u in the H-repr
B=vector(#B,i,B[i]/abs(content(B[i])));
return([A,B]);       \\ new representation of the cone u*C=[Generators,Inequalities]
}


/*** INPUT: given a vector(v) and a element (elmnt)  */

/*** OUTPUT: verify if such element is in the vector given  */ 

vfind(v,elmnt)=
{my(l);
l=0;
for(j=1,length(v),
    if(v[j]==elmnt,l=j; break(1));   \\ comparation between two polymods if such elements belongs to a number field.
   );
return(l); \\it is the l-th position of vector v where is "elmnt", if l=0 then v not contain "elmnt" 
}

/******************************************************************************************************************************/
/*****************************************************************************/
/*                                                                          */
/*    3. We verify if two Q-rational polyhedral cones of dimension n         */
/*                  intersect on its interior.                               */
/*                                                                           */
/*****************************************************************************/

/*** INPUT: Given two cones: B=[[C1.gen,C1.inqs],[C2.gen,C2.inqs]], d=bnfinit(polynomial) */
/*** OUTPUT: return 1 if both has intersection on its interior and return 0 otherwise */ 

intCs(B,d)= 
{my(C1,C2,H1,H2,R,r);
[C1,H1]=B[1]; [C2,H2]=B[2];
r=1; \\ r=0 means that C1 and C2 doesn't intersect on its interior, r=1 otherwise. The ncheck(*) verify that there exists of n elements l.i
for(j=1,#H2,     
    R=AddC([H2[j],C1,H1],d);
    [C1,H1]=R; \\ new cone C1 (V-represen.) after of add at C1 the restriction H2[j]. H1 is its H-represen.
    if(ncheck(C1,d)==0, r=0; break(1));
   );
return(r);
}

/******************************************************************************************************************************************/
/*****************************************************************************/
/*                                                                           */
/*    4. Calculate the sustration of two Q-rational polyhedral cones         */
/*       of dimension n as union of cones not necessarily simplicials        */
/*                                                                           */
/*****************************************************************************/

/* Now we want to implemented an algorithm that allows us to find the different of two Q-rational polyhedral cone */
/* as (possibly empty) union of Q-rational  such polyhedral cones are not necessarily simplicials */

/*** INPUT: Given two cones C1 and C2 with intersection on their interiors */
/*** v=[v[1],v[2]]=[[R-rep.,H-rep.], [R-rep.,H-rep.]]; d=bnfinit(polynomial) */

/*** OUTPUT: return the difference of this two cones as finite union of cones */
/**** such that these cones only has intersection between their facets***/ 

StrC(v,d)=  
{my(N,D,w);
N=v[2][2];     \\ N is an H-repre. of v[2].
D=vector(#N);
D[1]=StrC1([v[1],[-N[1]]],d);
for(j=2,#N,
    w=vector(j,i,N[i]); w[j]=-N[j]; D[j]=StrC1([v[1],w],d);
    );
return(D); 
}
\\ Note: D are parts of the sustration of C1 with C2, this depend of order of the elements on N (H-representations of C2)
\\ and the number of n-dimensional part on this sustration D is at most #Facets of C2. 



/*** INPUT: list of H-repres that we want to add at one cone given: */
/*** v=[v[1], v[2]], where v[1]=[R-rep.,H-rep.] a cone and v[2]=[List of H-rep(inequalities) that we want to add at cone v] */
/*** d=bnfinit(polynomial) */

/*** OUTPUT: new cone with this list added */ 

StrC1(v,d)=   
{my(H,C,L,R);
C=v[1][1]; \\ V-repre. of a cone
H=v[1][2]; \\ its H-repre.
L=v[2];    \\ these are H-reprs. that we want add to cone [C,H].
for(j=1,#L,
    R=AddC([L[j],C,H],d); 
    [C,H]=R;     \\ new cone V-repres. and H-repres.
    );
return([C,H]);  
}


/*****************************************************************************************************************************/
/************************************************************************************/
/*                                                                                  */
/*       5. Removing intersections of lists of negative cones and of positive cones */
/*                              for a unit given.                                   */
/*                                                                                  */
/************************************************************************************/
/* Here we propose algorithm to delete the common interior of two lists (of lists) of (pos. and neg.) cones  with respect one unit fixed.*/

/* Given K=bnfinit(p)=Q(theta) a number field generator by an irreduc. polynomial "p" */
/* INPUT: L=[[N1,List_1],...,[Nl,List_l]] (negative cones) T=[[P1,list_1],..,[Ps,list_s]] (positive cones) */
/* each list List_j represent a list of subcones of the cone N_j (or P_i), such "List_j" can be thinked as a "polyhedral semicomplex" */
/* d=bnfinit(p); g is a totally positve unit in K */

/* OUTPUT: News lists L'=[[N1,List_1'],...,[Nl,List_l']] (negative cones) T'=[[P1,list_1'],..,[Ps,list_s']] (positive cones) */
/* NOTE: In the pratical in our initial step, we will beginning with a list of the form: list_i=[Ni] (and [Pi]) in L and T respectively. */
/* so we begin (with the trivial unit g=1): L=[ [N[j],[N[j]]] | j=1..#N];T=[ [P[j],[P[j]]] | j=1..#P ] */

SeplistCs(L,T,g,d)=      
{my(s,TG,t1,h1,h2,ha,hb);
s=#T; TG=vector(s,i);
h1=0; h2=0;
for(i=1,s,
    t1=getwalltime();
    [L,TG[i],ha,hb]=DListCs(L,T[i],g,d);
    h1=h1+ha; h2=h2+hb;
    print1([[i],getwalltime()-t1]);
   );
return([L,TG,h1,h2]); \\ h1= #number of posible pairs of subcones where was necessary made some separation (such value is not optimal necessa.)
}

/************************************************************************************************************************/
/* INPUT: L=[[N1,list_1],,...,[Nl,List_l]], T=[P,a list of cones] */
/* d=bnfinit(p); g is a totally positve unit in K */

/* OUTPUT: LG=[DiferenceListCs(list_1,T^(1),g),....,DiferenceListCs(list_l,T^(l),g)], where T^(j) means list of subcones in T obtained in */
/* each step of the function "DiferenceListCs" */

DListCs(L,T,g,d)=  
{my(l,LG,t1,h1,ha,h2,hb);
l=#L; LG=vector(l,i);
h1=0; h2=0;
for(j=1,l,
    [LG[j],T,ha,hb]=DiferenceListCs(L[j],T,g,d); \\ separation between two lists of cones
    h1=h1+ha; h2=h2+hb;
   );
return([LG,T,h1,h2]);
}

/************************************************************************************************************************/
/* INPUT: Lists of (disjoint) n-dimensional cones A=[N1,...,Nl], B=[P1,..,Ps]; g=unit;  d=bnfinit(p); Ni (resp. Pj) subcones of N (resp. P)*/
/* i.e A and B are semicomplexes*/
/* C1=[N,A]; C2=[P,B] */
/* d=bnfinit(p); g is a totally positve unit in K */

/* OUTPUT: This return difference of two lists of cones without intersection between their interiors by the action of the unit "g"  */

DiferenceListCs(C1,C2,g,d)=  
{my(p,a,l,s,A1,B1,GA,GB,w,v,N,A,P,B,ha,hb,GA1,GA2,GB1,GB2,M,M1);
[N,A]=C1;
[P,B]=C2;
p=d.pol;
l=#A;
s=#B;
A1=vector(l,i);
B1=vector(s,i);
ha=0;
hb=0;
a=intCs([mulc(g,N,p),P],d);  \\ verify if the interior (gN\cap P)°=empty
if(a==0, [GA,GB]=[[N,A],[P,B]], 
   for(i=1,l,
       A1[i]=[j|j<-[1..s], intCs([mulc(g,A[i],p),B[j]],d)==1]; \\ all the elements B[j] which has intersection with g*A[i].
       );
   for(j=1,s,
       B1[j]=[i|i<-[1..l], vfind(A1[i],j)!=0 ];
       );
   ha=vecsum(vector(l,j,length(A1[j])));
   hb=vecsum(vector(s,j,length(B1[j])));
   GA1=vector(l,i,[]); GA2=vector(l,i,[]); 
   for(i=1,l,
       if(#A1[i]==0,  \\ means that g*A[i] fixed has not intersection with any cone in the list B.
         GA1[i]=[A[i]];  
         );
       if(#A1[i]>0,   \\ otherwise
         v=[B[h]| h<-A1[i]];
         GA2[i]=DiferenceCones([A[i]],v,g^(-1),d);
         );
       );
    M=concat(GA1,GA2);
    if(M==[],GA=[],GA=concat(M)); 
    GB1=vector(s,j,[]); GB2=vector(s,j,[]);
    for(j=1,s,
        if(#B1[j]==0,  \\ means that g^(-1)*B[j] fixed has not intersection with any cone of the list A.
          GB1[j]=[B[j]]; 
          );
        if(#B1[j]>0,   \\ Otherwise
          w=[A[h]| h<-B1[j]];
           GB2[j]=DiferenceCones([B[j]],w,g,d);  
          );
       );
   M1=concat(GB1,GB2);
   if(M1==[],GB=[],GB=concat(M1)); 
   [GA,GB]=[[N,GA],[P,GB]];
  );
return([GA,GB,ha,hb]);
}


/************************************************************************************************************************/
/* INPUT: P0=[P] (n-dim. positive cone), B=[N1,...,Nr] (list of n-dim. cones disjoint except by lower-dimensional cones-"semicomplex") */
/* g= given a unit , d=bnfinit(p).*/

/* OUTPUT: Write the difference of P with the list (gN1,gN2,...,gNr) as a new (possibly empty) list of cones */

DiferenceCones(P0,B,g,d)=  
{my(p,A,N,N1,L,P,P1,C,L1,L2);
p=d.pol; A=P0;
for(i=1,#B, N=B[i]; N1=mulc(g,N,p);  \\ multiplication of g by the cone N.
    L1=vector(#A,j,[]); L2=vector(#A,j,[]); 
    for(j=1,#A,
        P=A[j];
        if(intCs([N1,P],d)==1, \\means the set ( (gN1)\cap P )° is not empty.
           P1=StrC([P,N1],d);
           C=[c|c<-P1, ncheck(c[1],d)!=0];  \\ Here we consider only n-DIMENSIONAL CONES.
           for(j=1,#C,C[j]=HV(C[j][1],d)); \\ Here return C[j]=[R.repre,H.repre]
           L2[j]=C, L1[j]=[P] ); 
       );
     A=concat(concat(L1,L2));  
   );
return(A); \\ represent the closure of the P\(gN1,gN2,...,gNr) as a list of subcones in P.
}


/*****************************************************************************************************************************/
/************************************************************************************/
/*                                                                                  */
/*       6. Adding some boundaries in each n-dim. rational cone                     */
/*          with respect to the vantage point e=(1,0,...,0)  in R^(r1)X(C)^(r2)     */
/*                which is based in the Colmez's trick                              */
/*                                                                                  */
/************************************************************************************/
/** Given the vantage point e1=(1,0,...,0) in R^(r1)X(C)^(r2) and an n-dimenional rational cone C=[V-repres.,H-repres.] in R^(r1)X(C)^(r2) */
/** Return a vector v=[vector of +1 or -1], where "+1" means that L(e1)>0 and "-1" means L(e1)<0, for each L: V --> R, L(x)=tr(wx) represent a inequality in the H-representation of C */

/*****************************************************************************************************************/
\\Similarly as [EF20, Section 4.3]:
\\ In each closed n-dimensional rational cone C=[V-repr., H-repr.] in the list L, some parts of its boundary need to be add to obtain a true fundamental domain. In this case we use the Colmez's trick. More precisely, if the set [w_1,...,w_h] (in K) define the H-repre. of C, thus C={x in X: L_j=tr(w_jx)>=0}, this induce the semi-closed cone D={x in X: L_i(x)>0, for i in A1 and L_i(x)>=0, for i in A1, L_i(x)>0, i in A2}, where A1={i \in {1,...,h}: L_i(e1)>0} and A2={i \in {1,...,h}: L_i(e1)<0}, e1=(1,0,...0) in X=R^(r1)xC^(r2) (here it is necessary that r1>0). 
/*****************************************************************************************************************/

/*** INPUT: L is a list of rational cones with V-repr. and H-repr. */

/*** OUTPUT: Return the same list L with a vector of sign in each cones which */ 
/*** represented by "+1" if a part of the facet is added in the cone given and the sign "-1" otherwise   */

ABoundary(L,d)=      \\ L=list of cones with both representations [R.repre, H.repre]
{my(p,P,v);
p=d.pol;
print1(" Adding boundary ...");
for(j=1,#L,
    P=L[j];      \\ P=[R.repre, H.repre]                 
    v=vector(#P[2],i,sign(conjvec(Mod(P[2][i],p))[1]));  
    L[j]=concat(P,[v]);
    );
print1(" Finished: ");
return(L);
}




/**************************************************************/
/* Now we want to add ALL the faces of each semi-closed cone that define a TRUE fundamental domain*/
ABoundaryFaces(P,d)=   \\P=[V-repre, H-repre,v]; v=vector of sign "+/-1" obtained in ABoundary().
{my(A,B,v,g,G,nf,F,n,S,h,b,C,E);
nf=d.nf;
n=d.r1+2*d.r2;
p=d.pol;
[A,B,v]=P;
\\v=vector(#B,i,sign(conjvec(Mod(B[i],p))[1]));
g=[i| i<-[1..#B], v[i]==+1]; \\ set of indexes in H-rep such L(e_1)>0.
G=vector(#g,i);
for(i=1,#g,
    G[i]=[j| j<-[1..#A], nfelttrace(nf, B[g[i]]*A[j])==0] \\ indexes of (n-1)-faces of L
    );
F=vector(n-1,j);
F[1]=G; 
for(j=1,n-2,
    h=F[j];
    S=[];
    for(i=1,#h,
        S=setunion(S,Set(lsf([n-j,h[i],A,G],d)));
        );
    F[j+1]=S;
   );
\\b=vector(#F,j,#F[j]);
C=vector(n-1,j);
for(j=1,n-1,
    E=F[j];
    if(#E>0, C[n-j]=vector(#E,j,vector(#E[j],i,A[E[j][i]])), C[n-j]=[]);
    );
return(C); \\ this is a vector of lists of all the proper faces in the boundary of P ordered by (n-1)-faces; (n-2)-faces;....;2-faces;1-faces
}


/*** INPUT: Given L=[set of index of face, Face of P, all the facets of P, V-repre. of P]; d=bnfinit(K)*/

/*** OUTPUT: list of all the facets of the face F ***/ 

lsf(L,d)=  
{my(nf,e,F,G,S,B,s,R);
nf=d.nf;
e=L[1]; \\ dimension of the face F
F=L[2]; \\ F represent one face of P such F is given as an V-repre.
R=L[3]; \\ V-repr. of the cone P
G=L[4]; \\ list of all facets  of P as an V-repre.
S=[];
for(j=1,#G,
    s=setintersect(F,G[j]);
    if(#s>0,
      B=vector(#s,i,nfalgtobasis(nf,R[s[i]]));
      B=mattranspose(Mat(B));
      if(matrank(B)==e-1, S=concat(S,[s])); \\ "s" represent a facet of the face F given on P
      );
   );
return(S); \\ list of all the FACETS (dim=e-1) of the face F (dim=e).
}




