import { AtomicBlockUtils, EditorState } from 'draft-js';

export function insertImageBlock(editorState) {
	const contentState = editorState.getCurrentContent();
	const contentStateWithEntity = contentState.createEntity(
		'IMAGE',
		'IMMUTABLE',
		{ url: null }
	);
	const entityKey = contentStateWithEntity.getLastCreatedEntityKey();
	const newEditorState = EditorState.set(editorState, {
		currentContent: contentStateWithEntity,
	});
	return AtomicBlockUtils.insertAtomicBlock(newEditorState, entityKey, ' ');
}
