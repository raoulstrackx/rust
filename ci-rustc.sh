#!/bin/bash -ex

repo_root=$(readlink -f $(dirname "${BASH_SOURCE[0]}"))

print_header() {
  title=$1
  echo "================[ ${title} ]================"
}

init_repository() {
  print_header "init repository"
  
  pushd ${repo_root}
  git submodule update --init --recursive
  popd
}

build_clang() {
  print_header "Building clang"
  
  pushd ${repo_root}
  if [ -z "$1" ] ; then
    build_dir=${repo_root}/clang-build
  else
    build_dir=$1
  fi
  
  if [ -z "$2" ] ; then
    llvm_dir=${repo_root}/src/llvm-project/llvm
  else
    llvm_dir=$2
  fi
  
  rm ${build_dir}/clang.tar || true
  rm -r ${build_dir} || true
  mkdir ${build_dir}
  pushd ${build_dir}
  
  # Intel's LVIv4 patches introduces a dependency on the Hexagon hardware. We need to build this as well. This dependency is removed in later version (which we don't use yet)
  cmake -DLLVM_TARGETS_TO_BUILD="Hexagon;X86" -DLLVM_ENABLE_PROJECTS=clang -DCMAKE_BUILD_TYPE=Release -G "Unix Makefiles" ${llvm_dir}
  make -j 7 clang
  
  tar -cf ${build_dir}/clang.tar ${build_dir}/lib ${build_dir}/bin
  
  popd
  popd
}

build_libunwind() {
  build_dir=$1
  clang=$2

  print_header "Building libunwind"
 
  rm -rf ${build_dir} || true
  mkdir ${build_dir}
  pushd ${build_dir}
  export CC=${clang}
  export CXX=${clang}
  
  ${repo_root}/src/ci/docker/dist-various-2/build-x86_64-fortanix-unknown-sgx-toolchain.sh "800f95131fe6acd20b96b6f4723ca3c820f3d379"
  popd

  echo "libunwind located at: ${repo_root}/libunwind-build/"
}

build_rustc() {
  install_dir=$1
  
  print_header "Building rustc"
  
  pushd ${repo_root}

  rm ${repo_root}/config.toml || true
  rm ${repo_root}/build || true
  rm -r ${install_dir} || true
  rm ${repo_root}/rustc.tar || true

  git submodule update --init --recursive
  
  mkdir ${install_dir} || true
  ./configure --target="x86_64-unknown-linux-gnu,x86_64-fortanix-unknown-sgx" --prefix="${install_dir}" --disable-manage-submodules --enable-lld --disable-docs

  export X86_FORTANIX_SGX_LIBS=${repo_root}/libunwind-build/
  export PATH=$PATH:${repo_root}/src/llvm-project/compile-lfence/
  ${repo_root}/x.py build
  ${repo_root}/x.py install
  
  tar -cf ${repo_root}/rustc.tar ${install_dir}
  echo "Rust compiler ready in: ${install_dir}"
  
  popd
}

init_repository
build_clang "${repo_root}/clang-build"
build_libunwind "${repo_root}/libunwind-build" "${repo_root}/src/llvm-project/clang-build/bin/clang"
build_rustc "${repo_root}/rust-build"

