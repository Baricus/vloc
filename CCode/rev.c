/*
 * rev.c - Miles Shamo
 *
 * A short function in C defining a list
 * and the ability to reverse it.
 *
 */

#include <stdlib.h> // for NULL
#include <stdio.h>

// Node structure
typedef struct node {
	int val;
	struct node * next;
} node;


// list reverse stuff
node * rev_list_internal(node *prev, node *cur) {
	// end of list, so return head
	if (cur == NULL) {
		return prev;
	}

	// otherwise, swap pointers and continue
	node * temp = cur->next;
	cur->next = prev;

	// recurse for the new head
	return rev_list_internal(cur, temp);
}

node * rev_list(node *head) {
	return rev_list_internal(NULL, head);
}


// general list ops

/*
 * empty_node
 *
 * returns an empty node or crashes
 *
 */
node * empty_node() {
	node *ptr = malloc(sizeof(node));

	if (ptr == NULL) {
		exit(-1);
	}

	ptr->val = 0;
	ptr->next = NULL;

	// this should be fun to verify
	return ptr;
}

/*
 * prepend
 *
 * prepends a node to a given list, returning the
 * new head of the list
 *
 */
node * prepend(node * old_head, int i) {
	node * new_head = empty_node();

	new_head->val  = i;
	new_head->next = old_head;

	return new_head;
}

/*
 * check_list
 *
 */
int check_list(node * l1, node * l2) {
	if (l1 == NULL && l2 == NULL)
		return 1;
	if (l1 == NULL || l2 == NULL)
		return 0;

	return l1->val == l2->val && check_list(l1->next, l2->next);
}

#define LENGTH 10
int main() {
	// build a list and reverse array
	node *head = NULL;
	node *key  = NULL;
	for (int i = 1; i <= LENGTH; ++i) {
		head = prepend(head, i);
		key = prepend(key, 11 - i);
	}

	// reverse it
	node * rev = rev_list(head);
	
	// check it
	int res = check_list(rev, key);
	printf("%d\n", res);
	if (res) {
		printf("Success!\n");
	}
	return 0;
}
