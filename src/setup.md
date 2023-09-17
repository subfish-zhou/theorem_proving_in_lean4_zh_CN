安装Lean
---------------

本教程演示在Windows系统下如何安装Lean 4正式版。Linux和MacOS版本请参考Lean Manual。

## 基本安装

所有受支持平台的发布版本都可以在<https://github.com/leanprover/lean4/releases>中找到。

1. 使用Lean版本管理器[elan](https://github.com/leanprover/elan)代替下载文件和手动设置路径。在elan的[Github仓库](https://github.com/leanprover/elan)中下载最新release，解压运行elan-init.exe，按照指示安装。默认安装位置是用户文件目录下的`.elan`文件夹，添加环境变量`你的用户文件目录\.elan\bin`。

> 可能出现以下报错*无法加载文件……因为在此系统上禁止运行此脚本*”。解决方案是
> 1.用管理员身份运行Powershell；
> 2.输入命令`set-Executionpolicy Remotesigned`，选择`Y`；
> 然后就可以正常使用了。考虑到系统安全性，建议安装完成后将该选项改回默认值`N`。
> 效果如下图
> ![setuplean](images/setuplean.png)
> 由于本网站无法提供讨论区，欢迎向译者提供新的报错和解决方案，以丰富本页面。可邮件至[subfishzhou@gmail.com](mailto:subfishzhou@gmail.com)

2. 安装[git](https://gitforwindows.org/)。安装 [VS Code](https://code.visualstudio.com/)，并安装`lean4`扩展。

    ![installing the vscode-lean4 extension](images/code-ext.png)

3. 在终端中运行

```sh
$ elan self update  # 以防你下载的不是最新版elan
# 下载及应用最新的Lean4版本 (https://github.com/leanprover/lean4/releases)
$ elan default leanprover/lean4:stable
# 也可选择，只在当前目录下使用Lean4
$ elan override set leanprover/lean4:stable
```

4. 创建一个以 `.lean` 为扩展名的新文件，并写入以下代码：
    ```lean
    #eval Lean.versionString
    ```
    你会看到语法高亮。当你把光标放在最后一行时，在右边有一个“Lean信息视图”，显示已经安装的Lean版本。

    ![successful setup](images/code-success.png)

## 创建新Lean项目

用VS code打开一个新文件夹，你可以用两种方式创建新工程。

1. 在终端中运行

```
lake init <your_project_name>
```
以创建一个名为your_project_name的空白新工程。如果你想把你的Lean程序编译成可执行文件，在终端中运行`lake build`命令。

2. 如果你想在你的新工程中引用Mathlib4，在终端中运行

```
lake +leanprover-community/mathlib4:lean-toolchain new <your_project_name> math
```
（这个命令暂时无法让中国用户使用，等我找一个别的办法）