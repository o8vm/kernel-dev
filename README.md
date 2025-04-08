# Build Linux Kernel on macOS

## 1. Prerequisites
### Clone the kernel source 
```shell
git clone git://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git --depth 1 -b v6.14
```

### Install the necessary tools
```shell
brew install clang-format llvm lld make openssl pkg-config coreutils findutils gnu-tar gnu-sed gawk gnu-indent gnu-getopt grep
```

### Setup Environment:
```shell
PATH="$(brew --prefix llvm)/bin:$HOMEBREW_PREFIX/opt/make/libexec/gnubin:$HOMEBREW_PREFIX/opt/coreutils/libexec/gnubin:$HOMEBREW_PREFIX/opt/findutils/libexec/gnubin:$HOMEBREW_PREFIX/opt/gnu-tar/libexec/gnubin:$HOMEBREW_PREFIX/opt/gnu-sed/libexec/gnubin:$HOMEBREW_PREFIX/opt/gawk/libexec/gnubin:$HOMEBREW_PREFIX/opt/gnu-indent/libexec/gnubin:$HOMEBREW_PREFIX/opt/grep/libexec/gnubin:$PATH"
CPATH="$(brew --prefix openssl)/include"
LIBRARY_PATH="$(brew --prefix openssl)/lib"
```

## 2. Apply the patch
```shell
cd linux
patch < /path/to/mac_patch_6-14.patch
```

## 3. Build the kernel
```shell
make LLVM=1 defconfig
make LLVM=1 menuconfig  # then `General setup` -> `Local version - append to kernel release`
time make LLVM=1 ARCH=arm64 -j $(sysctl -n hw.logicalcpu) HOSTCFLAGS="-I./"
```

## 4. Run with QEMU
```shell
qemu-system-aarch64 -machine virt -m 512 -cpu cortex-a57 -kernel ./arch/arm64/boot/Image.gz -nographic
```
