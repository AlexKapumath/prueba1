
/* Updated 2021, March 08 */
/***********************************************************************************************************************/
/* The subject here is establish an algorirthm to determine a SIGNED fundamental domain for non-complex number fields. */
/* This is based in the works of Diaz y Diaz, Espinoza and Friedman:                                                   */
/* [DDF14] Diaz y Diaz and Friedman, "Signed fundamental domain for totally real number fields" (2014)  [MR4105945]    */
/* [EF20] Espinoza and Friedman, "Twisters and Signed fundamental domains of number fields" (2020)  [MR3198753]        */


\p 600 \\ realprecision, this real precision is necessary to compare the signs (+1 or -1) of each cone obtained below. 
/***********************************************************************************************************************/
/*****************************************************************************/
/*                                                                           */
/*                Computing signed fundamental domains for                   */
/*               Totally real number fields, i.e. (r1,r2)=(n,0)              */
/*                                                                           */
/*****************************************************************************/
/*********************************************************************************************************************/
/*** INPUT: bnf=bnfinit(polynomial) data of a number field K=Q(theta) given; U=their totally positive units */

/*** OUTPUT: A pair [N,P], where N and P denotes lists of generators in K_+ of the negative and positives cones respectively */
/*** Such pair [N,P] define a signed fundamental domain where their signs are sign(C)=-1 for each C in N and sign(C)=+1 for each C in P */
/*** Each (closed) cone C in N or P consisting of all linear combinations of v_1,...,v_e in K_+ with non-negative coefficients */
/*** In many cases #N + #P=(n-1)!, where n=[K:Q] the degree of K over Q */


signedfd1(U,bnf)=
{my(b,d,S,p,n,N,P,C,w,t1,e);
t1=getwalltime();
d=bnf;
b=sign(matdet(Mat(rpl(U,d)~)));
p=d.pol;
n=d.r1+2*d.r2;  \\ degree of polynomial p
S=lper(n-1);    \\ list of all the permutations in S_{n-1}.
N=[];
P=[];
for(l=1,#S,
   e=sgnc([S[l],U],d,b);
   if(e==1,
      C=[1];
      for(j=2,n,w=vector(j-1,i,U[S[l][i]]);C=concat(C,[prd(w,p)]));
      P=concat(P,[C]);
      );
   if(e==-1,
      C=[1];
      for(j=2,n,w=vector(j-1,i,U[S[l][i]]);C=concat(C,[prd(w,p)]));
      N=concat(N,[C]);
      );
);
print1([[#N,#P],getwalltime()-t1]); 
return([N,P]);
}


/*********************************************************************************************************************/
/*****************************************************************************/
/*                                                                           */
/*                Computing signed fundamental domains for                   */
/*                 all non-totally complex number fields                     */
/*                                                                           */
/*****************************************************************************/
/*********************************************************************************************************************/
/*** INPUT: bnf=bnfinit(polynomial) data of a number field K=Q(theta) given; U=totally positive units*/

/*** OUTPUT: A pair [N,P], where N and P denotes lists of generators in K_+ of the negative and positives cones respectively */
/*** Such pair [N,P] define a signed fundamental domain where their signs are sign(C)=-1 for each C in N and sign(C)=+1 for each C in P */
/*** Each (closed) cone C in N or P consisting of all linear combinations of v_1,...,v_e in K_+ with non-negative coefficients */
/*** In many cases #N + #P=(n-1)!*3^{r2}, where n=[K:Q] the degree of K over Q and r2=#of pairs of complex places*/


signedfd2(U,bnf)=
{my(SC,N,P,h,S,sg,C,L,t1,a);
t1=getwalltime();
SC=ComplexG(U,bnf); \\ the simplicial complex in Z^{n-1} with (n-1)!*3^{r2} simpliciales of dimension (n-1).
L=twisterG(bnf);    \\#L=3^r2 elements in k+, called twisters
a=signR(U,bnf);
N=[];
P=[];
h=length(SC);
for(j=1,h,
   S=SC[j];
   [sg,C]=signC(S,L,U,bnf,a);
   if(sg==1,P=concat(P,[C]));
   if(sg==-1,N=concat(N,[C])); \\ Cones with sign equal to zero is not consider in our "signed fundamental domain".
  );
print1([[#N,#P],getwalltime()-t1]); 
return([N,P]); 
}







/*****************************************************************************************************************************/
/*****************************************************************************************************************************/
/*** Now we describe all the functions mentioned in the two main routines above ***/
/*****************************************************************************************************************************/

/*List all the permutations:*/
/*** INPUT: "e" a natural number  */
/*** OUTPUT: list of all the permutations S_e   */ 
lper(e)=
{my(V);
V=vector(e!);
for(j=0,e!-1,
    V[j+1]=numtoperm(e,j);
   );
return(V);
}


/*Sign of a permutation given:*/
/*** INPUT: per= One permutation   */
/*** OUTPUT: Sign of the permutation given */ 
sgn(per)=
{my(s,n,M,L,Q,a);
s=per;n=#s;
M=matid(n);L=Vec(M);Q=vector(n);
for(j=1,n,
   Q[j]=L[s[j]];
);
a=sign(matdet(Mat(Q)));
return(a);
}

/*Representation of elements in a number field K into the space R^n  */
/*** INPUT: S=list of elements on K; d=bnfinit(polynomial)    */
/*** OUTPUT: representation on R^n of each element in S */ 

rpe(S,d)=     
{my(p,R);
p=d.pol;
R=vector(#S,i,Vec(conjvec(Mod(S[i],p))));
return(R);
}

/*Representation of totally positive elements in a totally real number field k into the logarithm space R^{n-1}  */
/*** INPUT: d=bnfinit(polynomial) data of a totally real number field K=Q(theta) given; S=list of totally positive elements in K_+ */
/*** OUTPUT: Representation in the logarithm space R^(n-1) of each element in S */ 

rpl(S,d)=  \\ only of K is totally real!
{my(R,R1,n,s,l);
R=vector(#S); \\ vector of zeros
l=log; n=d.r1+2*d.r2;
R1=rpe(S,d); \\ representation of the list on R^n
for(j=1,#S,
    s=R1[j]; R[j]=vector(n-1,i,l(s[i]));
   );
return(R);
}

/*** Return the product of one collection of elements in a number field K=Q(theta) given */
/*** INPUT: A=list of elements in K; poli=polynomial defining to the number field K   */
/*** OUTPUT: B=the product of the elements in A module K */ 
prd(A,poli)=  
{my(B);
B=A[1];
for(j=2,#A,B=lift(Mod(B*A[j],poli))); 
return(B);
}


/**********************************************************************************************************************************/
/* IN TOTALLY REAL NUMBER FIELDS */

/* Given a pair v=[v[1],v[2]] where v[1] is the permutation sigma and v[2] are the (n-1) totally positive units. */
/* Return the value w_{sigma}=(-1)^{n-1}*sign(sigma)*sign(det([f_{1,sigma},f_{2,sigma},...,f_{n,sigma}]))/sign(det(LOG(E_1)...LOG(E_{n-1})) */
/* That is, the routine below find the sign of the Colmez's cones that form a signed fundamental domain given in [DDF14, p. 966-967] */

/*** INPUT: v=[v[1],v[2]], b=sign(matdet(Mat(rpl(U,d)~))) and d=bnfinit(polynomial) */
/*** OUTPUT: The sign of each cone given en [DDF14, p. 966-967] ***/ 

sgnc(v,d,b)=  
{my(s,U,n,nf,p,E,e,L,M,a,c,w);
s=v[1];        \\ v[1] is a permutation in S_{n-1}
U=v[2];        \\ v[2]=topu(bnf) given the (n-1) units (in totally real fields).
n=#s+1;        \\ n is the degree of number field.
nf=d.nf;       \\ d.nf=bnf.nf
p=d.pol;
M=vector(n);   \\ vector of zeros in R^n.
M[1]=vector(n,i,1)~;         \\ vector of 1's in R^n.
E=vector(n);E[1]=1;
for(j=2,n,e=vector(j-1,i,U[s[i]]);E[j]=prd(e,p));
L=matrix(n,n, i,j, nfelttrace(nf,E[i]*E[j]));
if(matrank(L)==n,
for(j=2,n,
    w=vector(j-1,i,U[s[i]]);
    M[j]=rpe([prd(w,p)],d)[1]~; \\ is the product of e_{sigma(1)}*...*e_{sigma(j-1)}.
   );
  M=Mat(M);
  a=sign(matdet(M));
  c=((-1)^(n-1)*sgn(s)*a)/b;
 );
return(c);
}




/***************************************************************************************************************************************/
/* NOW IN NON-TOTALLY COMPLEX NUMBER FIELDS */
/******************************************************************************************************/
/*****   Firstly, we write an algorithm to generate a complex in R^{n-1}, where n=[k:Q],           ****/ 
/*****   with (n-1)!*3^{r2} simplices all (n-1)-dimensional, where r2=#(complex embedding places)  ****/
/*****   This is established in [EF20, Section 2.2, page 7]                                        ****/
/******************************************************************************************************/

/**********************************************************************************************************/
/* Given a number field K=Q(theta) */
/*** INPUT: vector "v" in R^r; "i" in [1...r,r+1,...n-1] ; U=elements on K_+; bnf=bnfinit(polynomial)*/
/*** OUTPUT: a value "R" in the complex plane   */ 

valW(v,i,U,bnf)=     \\  v=[v[1]..v[r]] in R^r, r=r_1+r_2-1, U=topu(bnf), for i=1,...,r,r+1,..n-1.
{my(r,r1,r2,S,R,n,D);
r1=bnf.r1;r2=bnf.r2;r=r1+r2-1;n=r1+2*r2;
S=rpe(U,bnf);     \\ length(S)=r;
D=vector(r,j,concat(vector(r1,t,S[j][t]),vector(r2,t,S[j][r1+2*t-1]))); \\ same to vector S without the conjugate places
if(0<i && i<=r, R=0,
   r<i && i<n, R=(3/(2*Pi))*vecsum(vector(r,l,v[l]*arg(D[l][i+1-r2]))),
   i<=0 || i>=n, error("the number " i " is not between " 1 " and " n-1));
return(R);
}


/**********************************************************************************************************/
\\ Given the simplex S=[v_1,..,v_p] (ordered), v_i in R^l returns a new simplex ordered respect to function A: R^l to (0,1].
\\ A(v):=1+valW(v)-ceil(valW(v)).
/** INPUT: Set of vertices */
/*** OUTPUT: Order the Set in function of "W" defined above */ 

ordA(S,U,bnf)=  
{my(F,T);
F=vecsort(vector(length(S),i,[1+valW(S[i],length(S[i])+1,U,bnf)-ceil(valW(S[i],length(S[i])+1,U,bnf)),i]));
T=vector(length(S));
for(h=1,length(F),T[h]=[S[F[h][2]],F[h][2]]);             \\F[h][2] represent the position on the original simplex S.
return(T);
}

/**********************************************************************************************************/
\\X=[v_1,\ldots,v_{p+1}] p-dimensional simplex, such that v_1>v_2>...>v_{p+1} where v is a vertex of X
\\ l is an integer, M1<= l < M2 for M1,M2 integer both, U=positive totally units.
\\ for t=1..n-1.
/*** INPUT: Given X be a complex in R^{d}, M1<M2 two integers*/
/*** OUTPUT: New in complex Y in R^{d+1}; see [EF20, Section 2.1]*/

Raising(X,M1,M2,U,bnf)=      \\ Here X is a complex of p-simplex in R^p. 
{my(t1,r1,r2,r,n,Z,Y,S0,p,C,S,T,j);
t1=getwalltime();
   r1=bnf.r1;
   r2=bnf.r2;
   r=r1+r2-1;                \\ rank of K
   n=r1+2*r2;
   Z=[];
 for(l=M1,M2-1,
   Y=[];
   for(h=1,length(X),
       S0=X[h];              \\ we take one p-simplex in R^p.      
       p=length(S0);
       C=vector(length(S0)); \\ set of (length(S0)+1) simplices in R^{p+1}.
       S=ordA(S0,U,bnf);     \\ new order of the simplex S. Using "ordA(--)"
       for(i=1,length(S),    \\ S[i] corresponds to take one vertex with label j in {1...p}.
          j=S[i][2];         \\ label corresponding to vertex S[i][1] of S
          T=concat(vector(j,t,[S[t][2],1-ceil(valW(S[t][1],length(S[t][1])+1,U,bnf))+l]),
                   vector(p-j+1,t,[S[t+j-1][2],1-ceil(valW(S[t+j-1][1],length(S[t+j-1][1])+1,U,bnf))+l-1]));
          T=vecsort(vector(length(T),i,[T[i][1],-T[i][2]]));          \\ order to the new simplex in R^{p+1}.
          C[i]=vector(length(T),s,concat(S0[T[s][1]],-T[s][2]));      \\ we consider the initial order in S0.
         );
      Y=concat(Y,C); 
      );
  Z=concat(Z,Y);
 );
print1([getwalltime()-t1]); 
return(Z);   \\ Z is a complex in R^{p+1}. #Z=(M2-M1)(p+1)(#X), where #X=number of p-simplex in X.
}

/**********************************************************************************************************/
/*** INPUT: U=totally positve units in k */
/*** OUTPUT: Return a complex in R^{n-1} */ 

ComplexG(U,bnf)=           \\ X=[[[1],[0]]] initial complex then return a complex in R^{n-1}, n=[K:Q].
{my(r1,r2,r,n,X);
r1=bnf.r1; r2=bnf.r2; r=r1+r2-1; n=r1+2*r2;
X=[[[1],[0]]];
for(j=1,r-1, X=Raising(X,0,1,U,bnf));
for(j=r,n-2, X=Raising(X,0,3,U,bnf));
return(X);      \\ Here this return to X as one complex in R^{n-1}, with #X=(n-1)!*3^{r2} (n-1)-dimensional simplices. See [EF20, Sect.2.2]
}



/********************************************************************************************************************************/
/* Now we need to write one algorithm to determine the generators of the cones and  */
/*  their signs given in [EF20, Section 2.4 and 2.5] which form a signed fundamental domain  */

/* For this, we need one function called "TWISTER FUNCTION", f:Z^{n-1} ---> k*, x|--> f(x) whose argument                       */
/* at the varios complex places are sufficiently close to those of certain roots of unity determine by x. See [EF20, Sect. 2.3] */
/********************************************************************************************************************************/

genn2(a)= \\ X=(Z/3Z)^r2, r2= #of complex places, a=r2, 
{my(S,P);
S=[0,1,2]; \\S=Z/3Z
P=[[0],[1],[2]];
while(#P!=3^a, P=concat(vector(3,i,vector(#P,j,concat(P[j],[S[i]])))); next);
return(P);
}


/*** Input: bnf=bnfinit(polynomial) data of a number fields K given */ 
/*** Output: List of twisters L=[b_1,...,b_{3^r2}] in K_+ which will be use to obtain the generators of the Cones given in [EF20] */

twisterG(bnf)=
{my(B,p,r1,r2,r,n,M,F,L,X,v1,v,w1,a,a1,a2,g,f);
B=bnf.zk; p=bnf.pol; r1=bnf.r1; r2=bnf.r2; r=r1+r2-1; n=r1+2*r2;
M=mattranspose(Mat(rpe(B,bnf)~));
if(r2>0,F=genn2(r2)); \\ F=(Z/3Z)^r2
L=vector(3^(r2),i);
if(r2>0,
   for(j=1,3^(r2),
    X=F[j];
    v1=[];
    for(j=1,r2,v1=concat(v1,[exp(2*Pi*I*X[j]/3),exp(-2*Pi*I*X[j]/3)]));
    v=concat(vector(r1,i,1),v1)~;          \\ vector in R_+^{r1}x(C^*)^{2*r2}.
    w1=matsolve(M,v);
    w1=bestappr(w1,5);                     \\ the best approx. rational of w1, whose denominator is limited by 100
    a=vecsum(vector(n,i,Vec(w1)[i]*B[i]));  \\ element in k
    a1=Vec(conjvec(Mod(a,p)));
    a2=concat(vector(r1,j,sign(a1[j])),vector(r2,j,sign(abs(a1[r1+2*j-1])))); \\ a2 contains the signs of the places in R^{r1}xC^{r2}.
    g=vector(r2,i);
    for(j=1,r2,
       f=arg(a1[r1+2*j-1]*exp(-2*Pi*I*X[j]/3));
       if(-Pi/6<f && f<Pi/6, g[j]=1, g[j]=0);
       );
    if(g==vector(r2,i,1) && a2==vector(r1+r2,i,1), a, error("the arg of respect to " X " is not in (-Pi/6,Pi/6)" " or such algebraic is not
      contained in k+"));
   L[j]=[X,a];
  ), L=[]);
return(L);
}


\\ Now we write a routine to find "the signs of the cones" in [EF20, equation (2.15)]
/***************************************************************************************************/
/*** INPUT: Simplex in Z^{n-1} */
/*** OUTPUT: sign of the det(V_D) */
 
signV(D)= \\ D=[v0,..vn] is a simplex in Z^{n-1}, then return the value of V_{D} (by the paper of Espinoza-Friedman!).
{my(M,d);
M=matconcat(vector(length(D)-1,i,D[i+1]-D[1])~);
d=matdet(M);
return(d);
}

/***************************************************************************************************/
/*** INPUT: U=Totally positive units */
/*** OUTPUT: Sign of the det(R) */ 

signR(U,bnf)= \\U=topu(bnfinit), it returns the value of R=[1;log(e_1);...;log(e_r)] in R^{r1+r2}.
{my(p,r1,r2,e,L,u,lu,R);
p=bnf.pol; r1=bnf.r1; r2=bnf.r2;
e=vector(r1+r2,i,1);
L=[e];
for(j=1,length(U),
    u=conjvec(Mod(U[j],p));  \\vector in R^{r1}xC^{2*r2}
    lu=concat(vector(r1,i,log(abs(u[i]))),vector(r2,i,log(abs(u[r1+2*i-1])))); \\ vector in R^{r1+r2}.
    L=concat(L,[lu]);
   );
R=matdet(Mat(L~));
return(R);
}

/***************************************************************************************************/
/*** INPUT: D=set of "n" elements in k */
/*** OUTPUT: sign of the det(W) */
 
signW(D,bnf)= \\ D=[d_1,...,d_{n}] where d_{i} is in k, it returns the value of det(D) in R^{n}.
{my(p,r1,r2,nf,n,W,a,b,L,t);
p=bnf.pol; nf=bnf.nf; r1=bnf.r1; r2=bnf.r2; n=r1+2*r2;
W=vector(n,i);
\\t=0;
L=matrix(n,n, i,j, nfelttrace(nf,D[i]*D[j]));
if(matrank(L)==n,
  for(j=1,n,
    a=conjvec(Mod(D[j],p)); \\ vector in R^{r1}*(C)^{2*r2} 
    b=vector(r1,i,a[i]);
    for(h=1,r2,b=concat(b,[real(a[r1+2*h-1]),imag(a[r1+2*h-1])]));   
    W[j]=b;
   );
t=matdet(Mat(W~));
);
return(t);
}

/***************************************************************************************************/
\\ D=[v1,..vn] is a simplex in Z^{n-1} 
/*** INPUT: D= simplex in Z^{n-1}; L=twisterG(bnf); U=totally positive units; bnf=bnfinit(polynomial) */
/*** OUTPUT: this returns the generators of the cone given in [EF20, p.10 equation (2.17)].  */
 
coneG(D,L,U,bnf)= 
{my(n,r,r2,C,p,ray,a,t);
n=length(D); p=bnf.pol; r=bnf.r1+bnf.r2-1; r2=bnf.r2;
C=vector(n,i);
for(j=1,n,
    a=D[j];
    if(r2>0,
       a=lift(Mod(vector(r2,i,a[i+r]),3));
       t=[b[2]|b<-L, b[1]==a][1], t=1);      \\ t = twister element in L corresponding to "a"
    ray=lift(Mod(t*prod(i=1,r,U[i]^(D[j][i])),p));
    C[j]=ray/abs(content(ray));
   );
return(C);  
}

/***************************************************************************************************/
/*** INPUT: a Simplex in Z^{n-1}; L=twisterG(bnf);  U=totally positive units; bnf=bnfinit(polynomial);sgR=signR(U,bnf) */
/*** OUTPUT: Return a pair [sign of C, C], C=the K-rational cone given in [EF20, equation (2.19)] */
 
signC(D,L,U,bnf,sgR)= 
{my(r2,C,a,b,c,sg);
r2=bnf.r2;
C=coneG(D,L,U,bnf);
a=sgR;
b=signV(D);
c=signW(C,bnf);
sg=(-1)^(r2*(r2-1)/2)*sign(a*b*c);
return([sg,C]); 
}

