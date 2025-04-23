# Makefile for Git and GitHub Automation
# Author: Claude
# Date: April 21, 2025

# Default target when running `make` with no arguments
.PHONY: help
help:
	@echo "\033[34mGit & GitHub Automation Makefile\033[0m"
	@echo "Usage: make [command] [options]"
	@echo ""
	@echo "Commands:"
	@echo "  init REPO=[repo-name]           - Initialize a new Git repository locally and on GitHub"
	@echo "  save MSG=[commit-message]       - Add all changes, commit, and push to remote"
	@echo "  branch NAME=[branch-name]       - Create and switch to a new branch"
	@echo "  pr TITLE=[title] DESC=[desc]    - Create a pull request (requires GitHub CLI)"
	@echo "  sync                            - Sync current branch with remote main/master"
	@echo "  clean                           - Remove untracked files and directories"
	@echo "  log NUM=[n]                     - Show last n commits (default: 5)"
	@echo "  status                          - Show repository status with enhanced output"
	@echo "  release VER=[version] MSG=[msg] - Create and push a new tag/release"
	@echo "  clone URL=[repo-url] DIR=[dir]  - Clone a repository with optimized settings"
	@echo ""
	@echo "Examples:"
	@echo "  make init REPO=my-project"
	@echo "  make save MSG=\"Fix login bug\""
	@echo "  make branch NAME=feature/user-auth"
	@echo "  make pr TITLE=\"Add user authentication\" DESC=\"Implements JWT auth\""
	@echo "  make release VER=1.0.0 MSG=\"Initial release\""

# Check if git is installed
check-git:
	@if ! command -v git &> /dev/null; then \
		echo "\033[31mError: Git is not installed\033[0m"; \
		echo "Please install Git first: https://git-scm.com/downloads"; \
		exit 1; \
	fi

# Check if GitHub CLI is installed
check-gh:
	@if ! command -v gh &> /dev/null; then \
		echo "\033[33mWarning: GitHub CLI is not installed\033[0m"; \
		echo "For PR creation, please install GitHub CLI: https://cli.github.com/"; \
		echo "Then authenticate with: gh auth login"; \
		exit 1; \
	fi
	@if ! gh auth status &> /dev/null; then \
		echo "\033[33mWarning: Not authenticated with GitHub CLI\033[0m"; \
		echo "Please run: gh auth login"; \
		exit 1; \
	fi

# Initialize a new repository
.PHONY: init
init: check-git
	@if [ -z "$(REPO)" ]; then \
		REPO=$$(basename "$$(pwd)"); \
		echo "\033[33mNo repository name provided. Using current directory name: $$REPO\033[0m"; \
	else \
		REPO=$(REPO); \
	fi; \
	echo "\033[34mInitializing repository: $$REPO\033[0m"; \
	git init; \
	if [ ! -f "README.md" ]; then \
		echo "# $$REPO" > README.md; \
		echo "\033[32mCreated README.md\033[0m"; \
	fi; \
	if [ ! -f ".gitignore" ]; then \
		echo "# OS generated files" > .gitignore; \
		echo ".DS_Store" >> .gitignore; \
		echo ".DS_Store?" >> .gitignore; \
		echo "._*" >> .gitignore; \
		echo ".Spotlight-V100" >> .gitignore; \
		echo ".Trashes" >> .gitignore; \
		echo "ehthumbs.db" >> .gitignore; \
		echo "Thumbs.db" >> .gitignore; \
		echo "" >> .gitignore; \
		echo "# IDE files" >> .gitignore; \
		echo ".idea/" >> .gitignore; \
		echo ".vscode/" >> .gitignore; \
		echo "*.sublime-project" >> .gitignore; \
		echo "*.sublime-workspace" >> .gitignore; \
		echo "" >> .gitignore; \
		echo "# Dependency directories" >> .gitignore; \
		echo "node_modules/" >> .gitignore; \
		echo "vendor/" >> .gitignore; \
		echo "" >> .gitignore; \
		echo "# Log files" >> .gitignore; \
		echo "*.log" >> .gitignore; \
		echo "npm-debug.log*" >> .gitignore; \
		echo "yarn-debug.log*" >> .gitignore; \
		echo "yarn-error.log*" >> .gitignore; \
		echo "" >> .gitignore; \
		echo "# Local env files" >> .gitignore; \
		echo ".env" >> .gitignore; \
		echo ".env.local" >> .gitignore; \
		echo ".env.development.local" >> .gitignore; \
		echo ".env.test.local" >> .gitignore; \
		echo ".env.production.local" >> .gitignore; \
		echo "\033[32mCreated .gitignore with common patterns\033[0m"; \
	fi; \
	git add .; \
	git commit -m "Initial commit"; \
	if command -v gh &> /dev/null && gh auth status &> /dev/null; then \
		echo "\033[34mCreating GitHub repository: $$REPO\033[0m"; \
		gh repo create "$$REPO" --source=. --public --push; \
		echo "\033[32mRepository created and pushed to GitHub: $$REPO\033[0m"; \
	else \
		echo "\033[33mGitHub CLI not available. Please create repository manually and then run:\033[0m"; \
		echo "git remote add origin git@github.com:USERNAME/$$REPO.git"; \
		echo "git branch -M main"; \
		echo "git push -u origin main"; \
	fi

# Save changes (add, commit, push)
.PHONY: save
save: check-git
	@if [ -z "$(MSG)" ]; then \
		datetime=$$(date "+%Y-%m-%d %H:%M:%S"); \
		MSG="Update - $$datetime"; \
		echo "\033[33mNo commit message provided. Using: $$MSG\033[0m"; \
	fi; \
	echo "\033[34mSaving changes...\033[0m"; \
	if git diff-index --quiet HEAD -- && [ -z "$$(git ls-files --others --exclude-standard)" ]; then \
		echo "\033[33mNo changes to commit\033[0m"; \
		exit 0; \
	fi; \
	git add .; \
	git commit -m "$(MSG)"; \
	branch=$$(git symbolic-ref --short HEAD); \
	echo "\033[34mPushing to remote branch: $$branch\033[0m"; \
	if git push origin "$$branch" 2>/dev/null; then \
		echo "\033[32mSuccessfully pushed changes to $$branch\033[0m"; \
	else \
		echo "\033[33mRemote branch doesn't exist. Creating it now...\033[0m"; \
		git push --set-upstream origin "$$branch"; \
		echo "\033[32mSuccessfully pushed changes to new branch: $$branch\033[0m"; \
	fi

# Create and switch to a new branch
.PHONY: branch
branch: check-git
	@if [ -z "$(NAME)" ]; then \
		echo "\033[31mError: Branch name required\033[0m"; \
		echo "Usage: make branch NAME=[branch-name]"; \
		exit 1; \
	fi; \
	echo "\033[34mCreating branch: $(NAME)\033[0m"; \
	if git show-ref --verify --quiet "refs/heads/$(NAME)"; then \
		echo "\033[33mBranch '$(NAME)' already exists\033[0m"; \
		echo "\033[34mSwitching to branch: $(NAME)\033[0m"; \
		git checkout "$(NAME)"; \
	else \
		git checkout -b "$(NAME)"; \
		echo "\033[32mCreated and switched to new branch: $(NAME)\033[0m"; \
	fi; \
	echo "\033[34mPushing branch to remote...\033[0m"; \
	git push --set-upstream origin "$(NAME)" && echo "\033[32mBranch pushed to remote\033[0m"

# Create a pull request
.PHONY: pr
pr: check-git check-gh
	@if [ -z "$(TITLE)" ]; then \
		branch=$$(git symbolic-ref --short HEAD); \
		TITLE="Pull request for $$branch"; \
		echo "\033[33mNo PR title provided. Using: $$TITLE\033[0m"; \
	fi; \
	if [ -z "$(DESC)" ]; then \
		DESC="Changes made in $$(git symbolic-ref --short HEAD)"; \
	fi; \
	echo "\033[34mCreating pull request...\033[0m"; \
	git push; \
	gh pr create --title "$(TITLE)" --body "$(DESC)"; \
	echo "\033[32mPull request created successfully\033[0m"

# Sync with main/master
.PHONY: sync
sync: check-git
	@echo "\033[34mSyncing with main branch...\033[0m"; \
	current_branch=$$(git symbolic-ref --short HEAD); \
	default_branch="main"; \
	if git show-ref --verify --quiet refs/remotes/origin/master; then \
		default_branch="master"; \
	fi; \
	echo "\033[34mFetching latest changes...\033[0m"; \
	git fetch origin; \
	if [ "$$current_branch" != "$$default_branch" ]; then \
		echo "\033[34mRebasing $$current_branch onto origin/$$default_branch...\033[0m"; \
		if git rebase "origin/$$default_branch"; then \
			echo "\033[32mSuccessfully rebased onto $$default_branch\033[0m"; \
		else \
			echo "\033[31mRebase conflict! Aborting rebase...\033[0m"; \
			git rebase --abort; \
			echo "\033[33mPlease merge manually:\033[0m"; \
			echo "git checkout $$default_branch"; \
			echo "git pull"; \
			echo "git checkout $$current_branch"; \
			echo "git merge $$default_branch"; \
			exit 1; \
		fi; \
	else \
		echo "\033[34mPulling latest changes for $$default_branch...\033[0m"; \
		git pull origin "$$default_branch"; \
	fi; \
	echo "\033[32mBranch is now in sync with $$default_branch\033[0m"

# Clean repository
.PHONY: clean
clean: check-git
	@echo "\033[33mWARNING: This will remove all untracked files and directories.\033[0m"
	@echo "\033[33mThese changes cannot be recovered.\033[0m"
	@read -p "Are you sure you want to continue? (y/n): " confirm; \
	if [[ $$confirm == [yY] || $$confirm == [yY][eE][sS] ]]; then \
		echo "\033[34mCleaning repository...\033[0m"; \
		echo "\033[34mFiles and directories that will be removed:\033[0m"; \
		git clean -fd --dry-run; \
		read -p "Proceed with removal? (y/n): " confirm2; \
		if [[ $$confirm2 == [yY] || $$confirm2 == [yY][eE][sS] ]]; then \
			git clean -fd; \
			echo "\033[32mRepository cleaned successfully\033[0m"; \
		else \
			echo "\033[33mClean operation cancelled\033[0m"; \
		fi; \
	else \
		echo "\033[33mClean operation cancelled\033[0m"; \
	fi

# Show git log
.PHONY: log
log: check-git
	@num=5; \
	if [ -n "$(NUM)" ]; then \
		num=$(NUM); \
	fi; \
	echo "\033[34mShowing last $$num commits:\033[0m"; \
	git log --oneline --graph --decorate --all -n $$num

# Show enhanced status
.PHONY: status
status: check-git
	@echo "\033[34mRepository Status:\033[0m"
	@echo "=============================="
	@branch=$$(git symbolic-ref --short HEAD 2>/dev/null || echo "(detached HEAD)"); \
	echo "\033[34mCurrent branch:\033[0m $$branch"; \
	remote_branch=$$(git for-each-ref --format='%(upstream:short)' $$(git symbolic-ref -q HEAD)); \
	if [ -n "$$remote_branch" ]; then \
		echo "\033[34mRemote branch:\033[0m $$remote_branch"; \
		ahead_behind=$$(git rev-list --left-right --count "$$branch...$$remote_branch" 2>/dev/null); \
		ahead=$$(echo "$$ahead_behind" | awk '{print $$1}'); \
		behind=$$(echo "$$ahead_behind" | awk '{print $$2}'); \
		if [ "$$ahead" -gt 0 ]; then \
			echo "\033[33mLocal is ahead by $$ahead commit(s)\033[0m"; \
		fi; \
		if [ "$$behind" -gt 0 ]; then \
			echo "\033[33mLocal is behind by $$behind commit(s)\033[0m"; \
		fi; \
		if [ "$$ahead" -eq 0 ] && [ "$$behind" -eq 0 ]; then \
			echo "\033[32mLocal is in sync with remote\033[0m"; \
		fi; \
	else \
		echo "\033[33mNo remote tracking branch set\033[0m"; \
	fi; \
	echo "\n\033[34mLocal Changes:\033[0m"; \
	git status -s; \
	stash_count=$$(git stash list | wc -l | tr -d ' '); \
	if [ "$$stash_count" -gt 0 ]; then \
		echo "\n\033[33mStashed changes: $$stash_count\033[0m"; \
	fi

# Create a release
.PHONY: release
release: check-git
	@if [ -z "$(VER)" ]; then \
		echo "\033[31mError: Version required\033[0m"; \
		echo "Usage: make release VER=[version] MSG=[message]"; \
		exit 1; \
	fi; \
	version=$(VER); \
	if [[ ! "$$version" =~ ^v ]]; then \
		version="v$$version"; \
	fi; \
	message="Release $$version"; \
	if [ -n "$(MSG)" ]; then \
		message=$(MSG); \
	fi; \
	echo "\033[34mCreating release: $$version\033[0m"; \
	git tag -a "$$version" -m "$$message"; \
	git push origin "$$version"; \
	if command -v gh &> /dev/null && gh auth status &> /dev/null; then \
		echo "\033[34mCreating GitHub release...\033[0m"; \
		gh release create "$$version" --title "$$version" --notes "$$message"; \
		echo "\033[32mGitHub release created: $$version\033[0m"; \
	else \
		echo "\033[32mTag pushed. Create release on GitHub manually if needed.\033[0m"; \
	fi

# Clone repository with optimized settings
.PHONY: clone
clone: check-git
	@if [ -z "$(URL)" ]; then \
		echo "\033[31mError: Repository URL required\033[0m"; \
		echo "Usage: make clone URL=[repo-url] DIR=[directory]"; \
		exit 1; \
	fi; \
	echo "\033[34mCloning repository: $(URL)\033[0m"; \
	if [ -z "$(DIR)" ]; then \
		git clone --depth 1 "$(URL)"; \
		directory=$$(basename "$(URL)" .git); \
	else \
		git clone --depth 1 "$(URL)" "$(DIR)"; \
		directory="$(DIR)"; \
	fi; \
	cd "$$directory" || exit 1; \
	echo "\033[34mFetching all branches...\033[0m"; \
	git fetch --all; \
	git config pull.rebase true; \
	git config fetch.prune true; \
	echo "\033[32mRepository cloned successfully to: $$directory\033[0m"; \
	echo "\033[34mCurrent branches:\033[0m"; \
	git branch -a