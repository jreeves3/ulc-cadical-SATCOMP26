ulc-cadical contains a preprocessor for unique literal clause (ULC) and exclusive literal clause (XLC) encoding within CaDiCaL. This preprocessor is built into CaDiCaL and called after other preprocessing techniques such as lucky search, but before the CDCL loop is entered. 

Changes from last year's SAT Competition submission:

- option for variable freezing 
- option for ulc reencoding before or after preprocessing
- implemented in newest version of CaDiCaL (3.0.0)

The main branch of CaDiCaL is available at https://github.com/arminbiere/cadical

Build Cadical

  > cd cadical ; ./configure && make
  OR
  > sh build.sh

Run Cadical with sequential counter encoding of ULCs with alignment on alignable formulas

  > ./build/cadical <form> proof --ulc=1 --ulctype=3 -t <timeout> 

Releveant options: 

--ulc=[0,1]      : 1 to perform reencoding of ulcs in preprocessing

--ulcalign=[0,1] : 0 for no alignment

--ulcelim=[0,1]  : 1 for variable elimination, transforming sequential counter to order encoding 

--ulcexit=[0,1]  : 1 to exit solver after preprocessing

--ulctype=[1,3]  : 1 for ULC detection, 2 for pairwise, 3 for hybrid (full XLC detection)

--ulcaligntype=[0,1,2] : 0 encode no matter alignment, 1 only encode alignable formula (skip preprocessing otherwise), 2 only encode alignable and independent formula

--ulcfreeze=[0,1] : 1 freeze new variables added during reencoding
