FindWordProperty:=function(g,maxrad,prop)
local gens,invmap,i,j,new,n,mo,e,d,w,from,to,lgn,wp,pos,r,nams,k,c,s,stop;
  stop:=ValueOption("findall")<>true;
  gens:=ShallowCopy(GeneratorsOfGroup(g));
  invmap:=[];
  nams:=List([1..Length(gens)],x->CHARS_LALPHA{[x]});
  for i in [1..Length(gens)] do
    new:=gens[i]^-1;
    if gens[i]=new then
      invmap[i]:=i;
    else
      Add(gens,new);
      Add(nams,UppercaseString(nams[i]));
      invmap[i]:=Length(gens);
      invmap[Length(gens)]:=i;
    fi;
  od;
  Add(invmap,0); # for no generator case
  mo:=2^(LogInt(Length(invmap),2)+1); # modulus we work with

  n:=Length(gens);
  
  e:=[One(g)];
  d:=NewDictionary(e[1],true,g);
  AddDictionary(d,e,1);
  w:=[Length(invmap)];
  to:=0;

  for r in [1..maxrad] do
    Print("radius=",r,"\n");
    # extend sphere of last length
    from:=to+1;
    to:=Length(e);
    for i in [from..to] do
      lgn:=w[i] mod mo; # last generator in product
      wp:=w[i]*mo;
      # run through all gens but the inverse of last factor
      for j in Difference([1..n],[invmap[lgn]]) do
        new:=e[i]*gens[j];
        pos:=LookupDictionary(d,new);
        if pos=fail then
          Add(e,new);
          AddDictionary(d,new,Length(e));
          Add(w,wp+j);
          if prop(new) then

            c:=Reversed(CoefficientsQadic(w[Length(w)],mo));
            s:="";
            for k in [2..Length(c)] do
              s:=Concatenation(s,nams[c[k]]);
            od;
            Print("Found:",s,"\n");
            if stop then
              Error("found!");
            fi;
          fi;
        fi;
      od;
    od;
  od;

end;
