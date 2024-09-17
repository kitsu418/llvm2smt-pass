add_llvm_pass_plugin(Llvm2SmtPass
    # List your source files here.
    llvm2smt.cc
)

target_link_libraries(Llvm2SmtPass PRIVATE Z3)