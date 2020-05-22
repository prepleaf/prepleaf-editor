import { Map } from 'immutable';
import React from 'react';
import PropTypes from 'prop-types';
import {
	Editor,
	EditorState,
	convertFromRaw,
	convertToRaw,
	RichUtils,
	getDefaultKeyBinding,
	KeyBindingUtil,
} from 'draft-js';
import 'draft-js/dist/Draft.css';
import 'katex/dist/katex.min.css';

import TeXBlock from './TeXBlock';
import ImageBlock from './ImageBlock';
import { insertTeXBlock } from './modifiers/insertTeXBlock';
import { removeTeXBlock } from './modifiers/removeTeXBlock';
import {
	insertInlineEquation,
	INLINE_EQUATION,
} from './modifiers/insertInlineEquation';
import { insertImageBlock } from './modifiers/insertImageBlock';
import decorators from './decorators';
import InlineEquation from './components/InlineEquation';
import './main.css';

const customStyleMap = {
	super: { verticalAlign: 'super', fontSize: '.8rem' },
	sub: { verticalAlign: 'sub', fontSize: '0.8rem' },
	equation: { marginLeft: '1px', marginRight: '1px', fontStyle: 'italic' },
};

const { hasCommandModifier } = KeyBindingUtil;

const keyBindingFn = (e) => {
	console.log(e.keyCode);
	if (e.keyCode === 120) {
		return 'insert_image';
	}
	if (hasCommandModifier(e)) {
		if (e.keyCode === 188) {
			e.preventDefault();
			return 'sub';
		}
		if (e.keyCode === 190) {
			e.preventDefault();
			return 'super';
		}
		if (e.keyCode === 69) {
			e.preventDefault();
			return 'equation';
		}
	}
	return getDefaultKeyBinding(e);
};

export class TeXEditor extends React.Component {
	constructor(props, context) {
		super(props, context);

		const { rawContent } = props;
		let contentEditorState;
		if (typeof rawContent === 'undefined') {
			contentEditorState = EditorState.createEmpty(decorators);
		} else {
			let modifiedRawContent;
			if (typeof rawContent === 'object') {
				modifiedRawContent = {
					entityMap: {},
					blocks: [],
					...rawContent,
				};
			} else {
				modifiedRawContent = {
					entityMap: {},
					blocks: [],
					...JSON.parse(rawContent),
				};
			}
			contentEditorState = EditorState.createWithContent(
				convertFromRaw(modifiedRawContent)
			);
		}

		this.state = {
			editorState: contentEditorState,
			liveTeXEdits: Map(),
			imageEdits: Map(),
		};

		this._focus = () => this.editorRef.focus();
		this._onChange = (editorState) => this.setState({ editorState });

		this._toggleName = (editorState, name) => {
			this._onChange(RichUtils.toggleInlineStyle(editorState, name));
		};

		this._handleKeyCommand = (command, editorState) => {
			if (['super', 'sub'].indexOf(command) > -1) {
				this._toggleName(editorState, command);
				return true;
			}
			if ('equation' === command) {
				this.markAsInlineEquation();
			}

			if ('insert_image' === command) {
				this._insertImage();
			}

			var newState = RichUtils.handleKeyCommand(editorState, command);
			if (newState) {
				this._onChange(newState);
				return true;
			}
			return false;
		};

		this._removeTeX = (blockKey) => {
			var { editorState, liveTeXEdits, imageEdits } = this.state;
			this.setState({
				liveTeXEdits: liveTeXEdits.remove(blockKey),
				imageEdits: imageEdits.remove(blockKey),
				editorState: removeTeXBlock(editorState, blockKey),
			});
		};

		this._insertTeX = () => {
			this.setState({
				liveTeXEdits: Map(),
				editorState: insertTeXBlock(this.state.editorState),
			});
		};
	}
	markAsInlineEquation = () => {
		this.setState({
			editorState: insertInlineEquation(this.state.editorState),
		});
	};
	toggleSuper = (e) => {
		e.preventDefault();
		e.stopPropagation();
		const { editorState } = this.state;
		this._toggleName(editorState, 'super');
	};
	toggleSub = () => {
		const { editorState } = this.state;
		this._toggleName(editorState, 'sub');
	};
	toggleEquation = () => {
		const { editorState } = this.state;
		this._toggleName(editorState, 'equation');
	};

	_insertImage = () => {
		this.setState({
			imageEdits: Map(),
			editorState: insertImageBlock(this.state.editorState),
		});
	};
	get value() {
		const { editorState } = this.state;
		return {
			rawContent: convertToRaw(editorState.getCurrentContent()),
		};
	}

	_blockRenderer = (block) => {
		const { getImagePolicy } = this.props;
		if (block.getType() === 'atomic') {
			const contentState = this.state.editorState.getCurrentContent();
			const type = contentState.getEntity(block.getEntityAt(0)).getType();
			if (type === 'TOKEN') {
				return {
					component: TeXBlock,
					editable: false,
					props: {
						onStartEdit: (blockKey) => {
							var { liveTeXEdits } = this.state;
							this.setState({
								liveTeXEdits: liveTeXEdits.set(blockKey, true),
							});
						},
						onFinishEdit: (blockKey, newContentState) => {
							var { liveTeXEdits } = this.state;
							this.setState({
								liveTeXEdits: liveTeXEdits.remove(blockKey),
								editorState: EditorState.createWithContent(newContentState),
							});
						},
						onRemove: (blockKey) => this._removeTeX(blockKey),
					},
				};
			}

			if (type === 'IMAGE') {
				return {
					component: ImageBlock,
					editable: false,
					props: {
						onStartEdit: (blockKey) => {
							var { imageEdits } = this.state;
							this.setState({
								imageEdits: imageEdits.set(blockKey, true),
							});
						},
						onFinishEdit: (blockKey, newContentState) => {
							var { imageEdits } = this.state;
							this.setState({
								imageEdits: imageEdits.remove(blockKey),
								editorState: EditorState.createWithContent(newContentState),
							});
						},
						onRemove: (blockKey) => this._removeTeX(blockKey),
						getImagePolicy,
					},
				};
			}
			if (type === INLINE_EQUATION) {
				return {
					component: InlineEquation,
				};
			}
		} else if (block.getType() === 'unstyled') {
			block.findEntityRanges(
				(v) => {
					if (v.getEntity()) {
						return true;
					}
					return false;
				},
				(start, end) => {
					// console.log(start, end);
					// console.log(block.getEntityAt(start));
				}
			);
		}
		return null;
	};

	resetEditor() {
		let contentEditorState = EditorState.createEmpty();
		this.setState({
			editorState: contentEditorState,
			liveTeXEdits: Map(),
		});
	}

	componentDidMount() {
		const { customRef } = this.props;
		customRef && customRef(this);
	}
	componentWillUnmount() {
		const { customRef } = this.props;
		customRef && customRef(null);
	}
	/**
	 * While editing TeX, set the Draft editor to read-only. This allows us to
	 * have a textarea within the DOM.
	 */
	render() {
		const { readOnly } = this.props;
		if (readOnly) {
			return (
				<div>
					<Editor
						customStyleMap={customStyleMap}
						blockRendererFn={this._blockRenderer}
						editorState={this.state.editorState}
						handleKeyCommand={this._handleKeyCommand}
						keyBindingFn={keyBindingFn}
						onChange={this._onChange}
						readOnly={
							readOnly ||
							this.state.liveTeXEdits.count() ||
							this.state.imageEdits.count()
						}
						ref={this.handleEditorRef}
						spellCheck={true}
					/>
				</div>
			);
		}
		return (
			<div className="prepleaf-editor">
				<div className="TeXEditor-toolbar">
					{/* <button onMouseDown={this.markAsInlineEquation}>
						Mark as inline equation
					</button> */}
					<button
						onMouseDown={this.toggleEquation}
						className="TeXEditor-insert-button"
					>
						inline equation
					</button>
					<button onMouseDown={this.toggleSub} className="TeXEditor-insert-button">
						X<sub>2</sub>
					</button>
					<button onMouseDown={this.toggleSuper} className="TeXEditor-insert-button">
						X<sup>2</sup>
					</button>
					<button onMouseDown={this._insertTeX} className="TeXEditor-insert-button">
						Equation
					</button>
					<button
						onMouseDown={this._insertImage}
						className="TeXEditor-insert-button"
					>
						Image
					</button>
				</div>
				<div className="TeXEditor-root">
					<div
						className="TeXEditor-editor"
						style={{ border: 'solid 1px #777' }}
						onClick={this._focus}
					>
						<Editor
							customStyleMap={customStyleMap}
							blockRendererFn={this._blockRenderer}
							editorState={this.state.editorState}
							handleKeyCommand={this._handleKeyCommand}
							keyBindingFn={keyBindingFn}
							onChange={this._onChange}
							placeholder="Start a document..."
							readOnly={
								readOnly ||
								this.state.liveTeXEdits.count() ||
								this.state.imageEdits.count()
							}
							ref={this.handleEditorRef}
							spellCheck={true}
						/>
					</div>
				</div>
			</div>
		);
	}

	handleEditorRef = (ref) => {
		this.editorRef = ref;
	};
}

TeXEditor.propTypes = {
	readOnly: PropTypes.bool.required,
};

TeXEditor.defaultProps = {
	readOnly: false,
};

export default TeXEditor;
