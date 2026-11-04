# DiophantineRigidity — início rápido no Mac

Este é um repositório **independente** de MahlerLean. Não extraia o ZIP dentro da pasta do projeto anterior.

1. Extraia `DiophantineRigidity.zip` e mova a pasta `DiophantineRigidity` para `~/Developer/`.
2. No Terminal:

```bash
cd ~/Developer/DiophantineRigidity
command -v gh || brew install gh
gh auth status || gh auth login
bash scripts/publish_github.sh
```

O script inicia um novo Git, faz o primeiro commit com sua identidade Git local e cria `DiegoMarquesMath/DiophantineRigidity` como repositório público. Caso deseje privacidade inicial, altere `--public` para `--private` no script antes de executá-lo.

3. Para conferir os módulos iniciais:

```bash
lake exe cache get
bash scripts/check.sh
```

4. Opcionalmente, copie os arquivos **somente para uso local**, pois estão em `.gitignore`:

```bash
cp ~/Desktop/AuditoriaTH/ATH_rev.tex paper/
cp ~/Desktop/AuditoriaTH/ATH_rev.pdf paper/
bash scripts/check_source_hashes.sh
```

**Não faça `git add -f` nesses arquivos sem decidir publicar o manuscrito.** Seu trabalho anterior em `~/Developer/MahlerLeanATH` permanece intacto, inclusive seus commits e relatórios locais.

A conexão GitHub deste chat não possui uma ação para criar repositórios novos; por isso, esta última criação precisa ser disparada por você na conta GitHub pelo script.
