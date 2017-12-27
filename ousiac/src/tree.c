#include "tree.h"
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

// #define NDEBUG
#include <assert.h>

#define max(x, y) (((x) > (y)) ? (x) : (y))

struct tree* tree_init(TREE_TYPE x) {
	struct tree* t = malloc(sizeof(struct tree));
	if (!t) {
		return NULL;
	}
	t->info = x;
	t->parent = NULL;
	t->lchild = NULL;
	t->rsibling = NULL;
	return t;
}

// HELPERS
// =======

struct tree* tree_container_helper(struct tree* t0, struct tree* t1) {
	if (t0 == t1 || !t0) {
		return t0;
	}
	return tree_container_helper(t1, t0->parent);
}

bool tree_is_leaf(struct tree* t) { return !tree_is_inode(t); }

bool tree_is_inode(struct tree* t) { return t->lchild; }

bool tree_is_root(struct tree* t) { return !(t->parent); }

size_t tree_count_children(struct tree* t) {
	size_t n = 0;
	struct tree* pchild = t->lchild;
	while (pchild) {
		pchild = pchild->rsibling;
		n++;
	}
	return n;
}

size_t tree_count_siblings(struct tree* t) {
	size_t n = 0;
	struct tree* psibling = t->rsibling;
	while (psibling) {
		psibling = psibling->rsibling;
		n++;
	}
	return n;
}

struct tree** tree_siblings(struct tree* t) {
	size_t n = tree_count_siblings(t);
	struct tree** siblings = malloc(sizeof(struct tree*) * n);
	t = t->lchild;
	while (n > 0) {
		n--;
		siblings[n] = t->rsibling;
	}
	return siblings;
}

struct tree** tree_pedigree(struct tree* t) {
	size_t lvl = tree_level(t);
	struct tree** pedigree = malloc(sizeof(struct tree*) * lvl);
	while (lvl > 0) {
		lvl--;
		pedigree[lvl] = t->parent;
	}
	return pedigree;
}

size_t tree_depth(struct tree* node) {
	size_t depth = 0;
	while (node->parent) {
		node = node->parent;
		depth++;
	}
	return depth;
}

size_t tree_level(struct tree* t) { return tree_depth(t + 1); }

size_t tree_height(struct tree* t) {
	if (tree_is_leaf(t)) {
		return 0;
	} else if (tree_count_siblings(t) > 0) {
		return 1 + tree_height(t->lchild);
	} else {
		return max(tree_height(t->lchild), tree_height(t->rsibling));
	}
}

struct tree** tree_children(struct tree* t) {
	size_t n = tree_count_children(t);
	struct tree** children = malloc(sizeof(struct tree*) * n);
	t = t->lchild;
	while (n > 0) {
		n--;
		children[n] = t->rsibling;
	}
	return children;
}

void tree_swap(struct tree* t0, struct tree* t1) {
	struct tree* ttemp = t0;
	t0->parent = t1->parent;
	t1->parent = ttemp->parent;
	t0->rsibling = t1->rsibling;
	t1->rsibling = ttemp->rsibling;
}
/*
struct tree* tree_iter_prefix(struct tree* tree) {
    tree_iter_prefix(tree->lchild);
    if (tree->lchild == NULL) { return tree; }
}*/

int tree_kill_children(struct tree* tree) {
	tree_kill(tree->lchild);
	tree->lchild = NULL;
	return 0;
}

bool tree_are_siblings(struct tree* t0, struct tree* t1) {
	return tree_is_older_sibling(t0, t1) || tree_is_older_sibling(t1, t0);
}

bool tree_is_older_sibling(struct tree* older, struct tree* younger) {
	while (older) {
		if (older->rsibling == younger) {
			return true;
		}
		older = older->rsibling;
	}
	return false;
}

bool tree_is_ancestor(struct tree* ancestor, struct tree* descendant) {
	if (descendant->parent == ancestor) {
		return true;
	}
	return tree_is_ancestor(ancestor, descendant->parent);
}

void tree_kill(struct tree* t) {
	if (!t)
		return;
	tree_kill(t->lchild);
	tree_kill(t->rsibling);
	free(t);
}

size_t tree_size(struct tree* t) {
	if (tree_is_leaf(t)) {
		return 1;
	}
	return 1 + tree_size(t->lchild) + tree_size(t->rsibling);
}

struct tree* tree_container(struct tree* t0, struct tree* t1) {
	if (!t1) {
		return NULL;
	} // t0 is checked by tree_container_helper
	return tree_container_helper(t0, t1);
}

int tree_prepend_child(struct tree* tree, int info) {
	tree->lchild = &(struct tree){
		.info = info, .parent = tree, .lchild = NULL, .rsibling = tree->lchild,
	};
	return 0;
}
